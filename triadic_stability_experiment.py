"""
Triadic Stability Barrier Experiment

Operationalizes PCTA impossibility theorem into measurable architecture consequences.

From PCTA.v: Affine triadic aggregators satisfying identity law must have d=2,
yielding diagonal Lipschitz constant 3/2. Non-affine operators escape this barrier.

Tests whether this manifests as measurable differences in gradient stability and
adversarial robustness in vision transformers.

Output: Raw JSON data for all metrics across experimental conditions.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import torchvision
import torchvision.transforms as transforms
from torch.utils.data import DataLoader
from torch.optim import AdamW
from torch.optim.lr_scheduler import CosineAnnealingLR
import numpy as np
import json
import time
import sys
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict
from pathlib import Path

print("=" * 80)
print("TRIADIC STABILITY EXPERIMENT")
print("=" * 80)
print(f"PyTorch version: {torch.__version__}")
print(f"CUDA available: {torch.cuda.is_available()}")
if torch.cuda.is_available():
    print(f"CUDA device: {torch.cuda.get_device_name(0)}")
    print(f"CUDA memory: {torch.cuda.get_device_properties(0).total_memory / 1e9:.2f} GB")
else:
    print("WARNING: No CUDA device found, using CPU (will be slow)")
print("=" * 80)
sys.stdout.flush()


# ============================================================================
# Triadic Operators
# ============================================================================

def huber_rho(r: torch.Tensor, tau: float) -> torch.Tensor:
    """Huberized L1 loss."""
    abs_r = r.abs()
    quadratic_mask = (abs_r <= tau).float()
    return quadratic_mask * (0.5 * r * r) + (1 - quadratic_mask) * tau * (abs_r - 0.5 * tau)


def huber_grad(u: torch.Tensor, x: torch.Tensor, tau: float) -> torch.Tensor:
    """Gradient of Huber-ρ wrt u."""
    r = u - x
    abs_r = r.abs()
    mask = (abs_r <= tau).float()
    return mask * r + (1 - mask) * tau * r.sign()


def huber_hess(u: torch.Tensor, x: torch.Tensor, tau: float) -> torch.Tensor:
    """Hessian diagonal of Huber-ρ."""
    return ((u - x).abs() <= tau).float()


def soft_median_3(a: torch.Tensor, b: torch.Tensor, c: torch.Tensor,
                  tau: float = 1e-3, iters: int = 2) -> torch.Tensor:
    """
    Soft median via Huberized L1 minimization: argmin_u Σ ρ_τ(u - x_i)

    Properties:
    - Satisfies T(0,a,a) ≈ a (exact as τ→0)
    - Cyclic symmetry
    - Non-affine
    - Diagonal Lipschitz = 1.0
    """
    stacked = torch.stack([a, b, c], dim=-2)
    u = torch.median(stacked, dim=-2).values

    for _ in range(iters):
        g = huber_grad(u, a, tau) + huber_grad(u, b, tau) + huber_grad(u, c, tau)
        H = huber_hess(u, a, tau) + huber_hess(u, b, tau) + huber_hess(u, c, tau)
        step = torch.where(H > 0, g / H.clamp_min(1e-6), torch.zeros_like(g))
        u = u - step

    return u


def hard_median_3(a: torch.Tensor, b: torch.Tensor, c: torch.Tensor) -> torch.Tensor:
    """Exact coordinate-wise median."""
    stacked = torch.stack([a, b, c], dim=-2)
    return torch.median(stacked, dim=-2).values


def affine_d2(a: torch.Tensor, b: torch.Tensor, c: torch.Tensor) -> torch.Tensor:
    """
    Affine aggregator with d=2: (a+b+c)/2

    From PCTA.v: Identity law T(0,x,x)=x forces d=2.
    Diagonal Lipschitz = 3/2.
    """
    return (a + b + c) / 2.0


def affine_d3(a: torch.Tensor, b: torch.Tensor, c: torch.Tensor) -> torch.Tensor:
    """
    Affine aggregator with d=3: (a+b+c)/3

    Barycentric (weights sum to 1).
    Does not satisfy T(0,x,x)=x.
    Diagonal Lipschitz = 1.0.
    """
    return (a + b + c) / 3.0


@torch.no_grad()
def measure_diagonal_gain(aggregator_fn, d_model: int = 64, n_samples: int = 1000,
                         device: str = 'cuda') -> float:
    """
    Empirical diagonal Lipschitz: L_Δ = max_{x≠0} |T(x,x,x)|/|x|
    """
    print(f"  Measuring diagonal gain (n_samples={n_samples})...", end="", flush=True)
    gains = []
    for _ in range(n_samples):
        x = torch.randn(1, d_model, device=device)
        x_norm = x.norm(p=2)
        if x_norm > 1e-6:
            y = aggregator_fn(x, x, x)
            gain = (y.norm(p=2) / x_norm).item()
            gains.append(gain)
    result = max(gains) if gains else 0.0
    print(f" {result:.6f}")
    sys.stdout.flush()
    return result


@torch.no_grad()
def measure_identity_error(aggregator_fn, d_model: int = 64, n_samples: int = 100,
                          device: str = 'cuda') -> float:
    """Identity law error: |T(0,a,a) - a| / |a|"""
    print(f"  Measuring identity error (n_samples={n_samples})...", end="", flush=True)
    errors = []
    for _ in range(n_samples):
        a = torch.randn(1, d_model, device=device)
        zero = torch.zeros(1, d_model, device=device)
        result = aggregator_fn(zero, a, a)
        error = (result - a).norm(p=2).item()
        errors.append(error / (a.norm(p=2).item() + 1e-8))
    result = np.mean(errors)
    print(f" {result:.6f}")
    sys.stdout.flush()
    return result


# ============================================================================
# Vision Transformer with Triadic Attention
# ============================================================================

class TriadicAttention(nn.Module):
    """Attention with triadic aggregation instead of softmax."""

    def __init__(self, d_model: int, n_heads: int, aggregator: str, tau: float = 1e-3,
                 d_head: Optional[int] = None, dropout: float = 0.0):
        super().__init__()
        self.d_model = d_model
        self.n_heads = n_heads
        self.d_head = d_head or (d_model // n_heads)
        self.aggregator = aggregator
        self.tau = tau

        self.q_proj = nn.Linear(d_model, n_heads * self.d_head, bias=False)
        self.k_proj = nn.Linear(d_model, n_heads * self.d_head, bias=False)
        self.v_proj = nn.Linear(d_model, n_heads * self.d_head, bias=False)
        self.o_proj = nn.Linear(n_heads * self.d_head, d_model, bias=False)
        self.dropout = nn.Dropout(dropout)

        if aggregator == 'affine_d2':
            self.aggregate = affine_d2
        elif aggregator == 'affine_d3':
            self.aggregate = affine_d3
        elif aggregator == 'median_hard':
            self.aggregate = hard_median_3
        elif aggregator == 'median_soft':
            self.aggregate = lambda a, b, c: soft_median_3(a, b, c, tau=tau)
        else:
            raise ValueError(f"Unknown aggregator: {aggregator}")

    def forward(self, x: torch.Tensor, mask: Optional[torch.Tensor] = None) -> torch.Tensor:
        B, T, D = x.shape

        q = self.q_proj(x).view(B, T, self.n_heads, self.d_head).transpose(1, 2)
        k = self.k_proj(x).view(B, T, self.n_heads, self.d_head).transpose(1, 2)
        v = self.v_proj(x).view(B, T, self.n_heads, self.d_head).transpose(1, 2)

        scale = self.d_head ** -0.5
        scores = torch.einsum('bhtd,bhTd->bhtT', q, k) * scale

        if mask is not None:
            scores = scores.masked_fill(~mask, float('-inf'))

        self_mask = torch.eye(T, device=x.device, dtype=torch.bool)
        scores_masked = scores.masked_fill(self_mask.unsqueeze(0).unsqueeze(0), float('-inf'))
        top2_idx = scores_masked.topk(2, dim=-1).indices

        idx_j = top2_idx[..., 0]
        idx_k = top2_idx[..., 1]

        v_i = v
        v_j = v.gather(2, idx_j.unsqueeze(-1).expand(-1, -1, -1, self.d_head))
        v_k = v.gather(2, idx_k.unsqueeze(-1).expand(-1, -1, -1, self.d_head))

        y = self.aggregate(v_i, v_j, v_k)

        y = y.transpose(1, 2).contiguous().view(B, T, -1)
        out = self.o_proj(y)
        return self.dropout(out)


class StandardAttention(nn.Module):
    """Standard softmax attention."""

    def __init__(self, d_model: int, n_heads: int, d_head: Optional[int] = None, dropout: float = 0.0):
        super().__init__()
        self.d_model = d_model
        self.n_heads = n_heads
        self.d_head = d_head or (d_model // n_heads)

        self.q_proj = nn.Linear(d_model, n_heads * self.d_head, bias=False)
        self.k_proj = nn.Linear(d_model, n_heads * self.d_head, bias=False)
        self.v_proj = nn.Linear(d_model, n_heads * self.d_head, bias=False)
        self.o_proj = nn.Linear(n_heads * self.d_head, d_model, bias=False)
        self.dropout = nn.Dropout(dropout)

    def forward(self, x: torch.Tensor, mask: Optional[torch.Tensor] = None) -> torch.Tensor:
        B, T, D = x.shape

        q = self.q_proj(x).view(B, T, self.n_heads, self.d_head).transpose(1, 2)
        k = self.k_proj(x).view(B, T, self.n_heads, self.d_head).transpose(1, 2)
        v = self.v_proj(x).view(B, T, self.n_heads, self.d_head).transpose(1, 2)

        scale = self.d_head ** -0.5
        scores = torch.einsum('bhtd,bhTd->bhtT', q, k) * scale

        if mask is not None:
            scores = scores.masked_fill(~mask, float('-inf'))

        attn = F.softmax(scores, dim=-1)
        attn = self.dropout(attn)

        y = torch.einsum('bhtT,bhTd->bhtd', attn, v)
        y = y.transpose(1, 2).contiguous().view(B, T, -1)
        return self.o_proj(y)


class TransformerBlock(nn.Module):
    def __init__(self, d_model: int, n_heads: int, mlp_ratio: int, dropout: float,
                 use_triadic: bool, aggregator: Optional[str] = None, tau: float = 1e-3):
        super().__init__()
        self.norm1 = nn.LayerNorm(d_model)

        if use_triadic:
            self.attn = TriadicAttention(d_model, n_heads, aggregator, tau, dropout=dropout)
        else:
            self.attn = StandardAttention(d_model, n_heads, dropout=dropout)

        self.norm2 = nn.LayerNorm(d_model)
        d_ff = d_model * mlp_ratio
        self.ffn = nn.Sequential(
            nn.Linear(d_model, d_ff),
            nn.GELU(),
            nn.Dropout(dropout),
            nn.Linear(d_ff, d_model),
            nn.Dropout(dropout),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = x + self.attn(self.norm1(x))
        x = x + self.ffn(self.norm2(x))
        return x


class VisionTransformer(nn.Module):
    def __init__(self, d_model: int, n_heads: int, n_layers: int, mlp_ratio: int,
                 num_classes: int, image_size: int, patch_size: int, dropout: float,
                 aggregator: str, tau: float = 1e-3):
        super().__init__()
        self.aggregator = aggregator

        n_patches = (image_size // patch_size) ** 2
        self.patch_embed = nn.Conv2d(3, d_model, kernel_size=patch_size, stride=patch_size)

        self.cls_token = nn.Parameter(torch.randn(1, 1, d_model) * 0.02)
        self.pos_embed = nn.Parameter(torch.randn(1, n_patches + 1, d_model) * 0.02)

        use_triadic = (aggregator != 'standard')
        self.blocks = nn.ModuleList([
            TransformerBlock(d_model, n_heads, mlp_ratio, dropout, use_triadic, aggregator, tau)
            for _ in range(n_layers)
        ])

        self.norm = nn.LayerNorm(d_model)
        self.head = nn.Linear(d_model, num_classes)

        self._init_weights()

    def _init_weights(self):
        for m in self.modules():
            if isinstance(m, nn.Linear):
                nn.init.trunc_normal_(m.weight, std=0.02)
                if m.bias is not None:
                    nn.init.zeros_(m.bias)
            elif isinstance(m, nn.LayerNorm):
                nn.init.ones_(m.weight)
                nn.init.zeros_(m.bias)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        B = x.shape[0]
        x = self.patch_embed(x).flatten(2).transpose(1, 2)
        cls_tokens = self.cls_token.expand(B, -1, -1)
        x = torch.cat([cls_tokens, x], dim=1)
        x = x + self.pos_embed

        for block in self.blocks:
            x = block(x)

        x = self.norm(x)
        return self.head(x[:, 0])


# ============================================================================
# Adversarial Evaluation
# ============================================================================

def pgd_attack(model: nn.Module, x: torch.Tensor, y: torch.Tensor,
               epsilon: float, alpha: float, steps: int) -> torch.Tensor:
    """PGD-l∞ adversarial attack."""
    was_training = model.training
    model.train()  # Need gradients

    x_adv = x.clone().detach() + torch.empty_like(x).uniform_(-epsilon, epsilon)
    x_adv = torch.clamp(x_adv, 0, 1)

    for _ in range(steps):
        x_adv = x_adv.detach().requires_grad_(True)
        logits = model(x_adv)
        loss = F.cross_entropy(logits, y)
        loss.backward()

        with torch.no_grad():
            grad = x_adv.grad
            x_adv = x_adv + alpha * grad.sign()
            x_adv = torch.min(torch.max(x_adv, x - epsilon), x + epsilon)
            x_adv = torch.clamp(x_adv, 0, 1)

    if not was_training:
        model.eval()

    return x_adv.detach()


def evaluate_robustness(model: nn.Module, loader: DataLoader, device: str,
                       epsilon: float, alpha: float, steps: int) -> Dict[str, float]:
    """Evaluate clean and adversarial accuracy."""
    print(f"  Evaluating robustness (PGD-linf, eps={epsilon:.4f})...", flush=True)
    model.eval()

    clean_correct = 0
    adv_correct = 0
    total = 0

    for i, (x, y) in enumerate(loader):
        x, y = x.to(device), y.to(device)

        logits = model(x)
        clean_correct += (logits.argmax(1) == y).sum().item()

        x_adv = pgd_attack(model, x, y, epsilon, alpha, steps)
        logits_adv = model(x_adv)
        adv_correct += (logits_adv.argmax(1) == y).sum().item()

        total += x.size(0)

        if (i + 1) % 10 == 0:
            print(f"    Batch {i+1}/{len(loader)}: Clean {clean_correct/total:.3f}, Adv {adv_correct/total:.3f}", flush=True)

    print(f"  Robustness eval complete.", flush=True)
    return {
        'clean_accuracy': clean_correct / total,
        'adversarial_accuracy': adv_correct / total,
        'robustness_gap': (clean_correct - adv_correct) / total,
    }


def measure_gradient_health(model: nn.Module, loader: DataLoader, device: str,
                           n_batches: int = 20) -> Dict[str, float]:
    """Measure gradient norm statistics."""
    print(f"  Measuring gradient health (n_batches={n_batches})...", end="", flush=True)
    model.train()
    grad_norms = []

    for i, (x, y) in enumerate(loader):
        if i >= n_batches:
            break

        x, y = x.to(device), y.to(device)
        logits = model(x)
        loss = F.cross_entropy(logits, y)
        loss.backward()

        total_norm = 0.0
        for p in model.parameters():
            if p.grad is not None:
                total_norm += p.grad.norm(2).item() ** 2
        grad_norms.append(total_norm ** 0.5)

        model.zero_grad()

    grad_norms = np.array(grad_norms)
    result = {
        'grad_norm_mean': float(grad_norms.mean()),
        'grad_norm_std': float(grad_norms.std()),
        'grad_norm_max': float(grad_norms.max()),
        'grad_explode_rate': float((grad_norms > 10.0).mean()),
    }
    print(f" mean={result['grad_norm_mean']:.4f}, max={result['grad_norm_max']:.4f}")
    sys.stdout.flush()
    return result


def measure_block_spectral_norm(block: nn.Module, x_sample: torch.Tensor,
                                n_iter: int = 5) -> float:
    """
    Estimate local spectral norm of residual block via power iteration on JVPs.

    Block: x ↦ x + Attention(LN(x))

    Power iteration approximates largest singular value of Jacobian at x_sample.
    This is the local Lipschitz constant of the block.

    Args:
        block: TransformerBlock module
        x_sample: Input point (B, T, D)
        n_iter: Number of power iterations

    Returns:
        Estimated spectral norm (local Lipschitz constant)
    """
    block.eval()

    # Random direction vector (same shape as input)
    v = torch.randn_like(x_sample)
    v = v / (v.norm() + 1e-8)

    for _ in range(n_iter):
        # Enable gradients for JVP computation
        x_sample_copy = x_sample.detach().requires_grad_(True)

        # Forward pass through block
        y = block(x_sample_copy)

        # Jacobian-vector product: J·v
        # This is equivalent to directional derivative
        jvp = torch.autograd.grad(y, x_sample_copy, v,
                                  create_graph=False, retain_graph=False)[0]

        # Normalize direction for next iteration
        v = jvp / (jvp.norm() + 1e-8)

    # Final JVP to get spectral norm estimate
    x_sample_copy = x_sample.detach().requires_grad_(True)
    y = block(x_sample_copy)
    jvp = torch.autograd.grad(y, x_sample_copy, v,
                             create_graph=False, retain_graph=False)[0]

    spectral_norm = jvp.norm().item()
    return spectral_norm


def measure_all_block_spectral_norms(model: VisionTransformer, loader: DataLoader,
                                     device: str, n_samples: int = 5) -> Dict[str, float]:
    """
    Measure spectral norms for all transformer blocks.

    Returns per-layer spectral norms and statistics.
    """
    print(f"  Measuring block spectral norms (n_samples={n_samples})...", end="", flush=True)
    model.eval()

    # Get a batch of data
    x, _ = next(iter(loader))
    x = x.to(device)

    # Patch embed to get token representations
    x = model.patch_embed(x).flatten(2).transpose(1, 2)
    cls_tokens = model.cls_token.expand(x.size(0), -1, -1)
    x = torch.cat([cls_tokens, x], dim=1)
    x = x + model.pos_embed

    # Take small batch for efficiency
    x = x[:n_samples]

    block_norms = []
    for i, block in enumerate(model.blocks):
        # Measure spectral norm of this block
        spec_norm = measure_block_spectral_norm(block, x, n_iter=5)
        block_norms.append(spec_norm)

        # Pass through block for next layer measurement
        with torch.no_grad():
            x = block(x)

    block_norms = np.array(block_norms)
    result = {
        'block_spectral_norm_mean': float(block_norms.mean()),
        'block_spectral_norm_max': float(block_norms.max()),
        'block_spectral_norm_std': float(block_norms.std()),
        'block_spectral_norms': block_norms.tolist(),
    }

    print(f" mean={result['block_spectral_norm_mean']:.4f}, max={result['block_spectral_norm_max']:.4f}")
    sys.stdout.flush()
    return result


# ============================================================================
# Training
# ============================================================================

def train_epoch(model: nn.Module, loader: DataLoader, optimizer: torch.optim.Optimizer,
                device: str, grad_clip: float, epoch: int) -> Dict[str, float]:
    model.train()
    loss_sum = 0.0
    correct = 0
    total = 0

    for i, (x, y) in enumerate(loader):
        x, y = x.to(device), y.to(device)
        logits = model(x)
        loss = F.cross_entropy(logits, y)

        optimizer.zero_grad()
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), grad_clip)
        optimizer.step()

        loss_sum += loss.item() * x.size(0)
        correct += (logits.argmax(1) == y).sum().item()
        total += x.size(0)

        if (i + 1) % 50 == 0:
            print(f"  Epoch {epoch}, Batch {i+1}/{len(loader)}: Loss={loss.item():.4f}, Acc={correct/total:.4f}", flush=True)

    return {'train_loss': loss_sum / total, 'train_accuracy': correct / total}


@torch.no_grad()
def evaluate(model: nn.Module, loader: DataLoader, device: str) -> Dict[str, float]:
    print(f"  Evaluating on test set...", end="", flush=True)
    model.eval()
    loss_sum = 0.0
    correct = 0
    total = 0

    for x, y in loader:
        x, y = x.to(device), y.to(device)
        logits = model(x)
        loss = F.cross_entropy(logits, y)

        loss_sum += loss.item() * x.size(0)
        correct += (logits.argmax(1) == y).sum().item()
        total += x.size(0)

    result = {'test_loss': loss_sum / total, 'test_accuracy': correct / total}
    print(f" Acc={result['test_accuracy']:.4f}")
    sys.stdout.flush()
    return result


def get_dataloaders(batch_size: int) -> Tuple[DataLoader, DataLoader]:
    """CIFAR-10 dataloaders."""
    print("Loading CIFAR-10 dataset...", flush=True)
    train_transform = transforms.Compose([
        transforms.RandomCrop(32, padding=4),
        transforms.RandomHorizontalFlip(),
        transforms.ToTensor(),
        transforms.Normalize((0.4914, 0.4822, 0.4465), (0.2023, 0.1994, 0.2010)),
    ])
    test_transform = transforms.Compose([
        transforms.ToTensor(),
        transforms.Normalize((0.4914, 0.4822, 0.4465), (0.2023, 0.1994, 0.2010)),
    ])

    train_dataset = torchvision.datasets.CIFAR10('./data', train=True, download=True, transform=train_transform)
    test_dataset = torchvision.datasets.CIFAR10('./data', train=False, download=True, transform=test_transform)

    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True, num_workers=0, pin_memory=True)
    test_loader = DataLoader(test_dataset, batch_size=batch_size, shuffle=False, num_workers=0, pin_memory=True)

    print(f"  Train: {len(train_dataset)} samples, {len(train_loader)} batches")
    print(f"  Test: {len(test_dataset)} samples, {len(test_loader)} batches")
    sys.stdout.flush()
    return train_loader, test_loader


# ============================================================================
# Experiment Driver
# ============================================================================

@dataclass
class Config:
    d_model: int = 128
    n_heads: int = 4
    n_layers: int = 6
    mlp_ratio: int = 4
    patch_size: int = 4
    dropout: float = 0.1

    batch_size: int = 2048
    epochs: int = 20
    lr: float = 3e-4
    weight_decay: float = 0.05
    grad_clip: float = 1.0

    measure_every: int = 5
    pgd_epsilon: float = 8.0 / 255.0
    pgd_alpha: float = 2.0 / 255.0
    pgd_steps: int = 10

    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'
    seed: int = 42


def run_single_experiment(aggregator: str, config: Config) -> Dict:
    """Run experiment for given aggregator."""
    print(f"\n{'='*80}")
    print(f"Aggregator: {aggregator}")
    print(f"{'='*80}")
    sys.stdout.flush()

    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed(config.seed)

    train_loader, test_loader = get_dataloaders(config.batch_size)

    print(f"Building VisionTransformer (aggregator={aggregator})...", flush=True)
    model = VisionTransformer(
        d_model=config.d_model,
        n_heads=config.n_heads,
        n_layers=config.n_layers,
        mlp_ratio=config.mlp_ratio,
        num_classes=10,
        image_size=32,
        patch_size=config.patch_size,
        dropout=config.dropout,
        aggregator=aggregator,
    )

    print(f"Moving model to device: {config.device}...", flush=True)
    try:
        model = model.to(config.device)
    except RuntimeError as e:
        print(f"ERROR moving model to {config.device}: {e}")
        print("Falling back to CPU")
        config.device = 'cpu'
        model = model.to(config.device)

    n_params = sum(p.numel() for p in model.parameters())
    print(f"Model parameters: {n_params:,}")
    sys.stdout.flush()

    optimizer = AdamW(model.parameters(), lr=config.lr, weight_decay=config.weight_decay)
    scheduler = CosineAnnealingLR(optimizer, T_max=config.epochs)

    print("\nPre-training measurements:")
    sys.stdout.flush()
    if aggregator != 'standard':
        agg_fn = model.blocks[0].attn.aggregate
        diagonal_gain = measure_diagonal_gain(agg_fn, config.d_model, device=config.device)
        identity_error = measure_identity_error(agg_fn, config.d_model, device=config.device)

        pre_metrics = {
            'pre_diagonal_gain': diagonal_gain,
            'pre_identity_error': identity_error,
        }
    else:
        pre_metrics = {}

    print(f"\nStarting training ({config.epochs} epochs)...")
    sys.stdout.flush()
    start_time = time.time()
    all_results = []
    best_acc = 0.0
    best_model_state = None

    for epoch in range(config.epochs):
        print(f"\n{'='*80}")
        print(f"Epoch {epoch+1}/{config.epochs}")
        print(f"{'='*80}")
        sys.stdout.flush()

        train_metrics = train_epoch(model, train_loader, optimizer, config.device, config.grad_clip, epoch+1)
        test_metrics = evaluate(model, test_loader, config.device)
        scheduler.step()

        epoch_data = {
            'epoch': epoch + 1,
            **train_metrics,
            **test_metrics,
        }

        if (epoch + 1) % config.measure_every == 0 or epoch == config.epochs - 1:
            print(f"\nComprehensive measurement at epoch {epoch+1}")
            sys.stdout.flush()

            rob_metrics = evaluate_robustness(
                model, test_loader, config.device,
                config.pgd_epsilon, config.pgd_alpha, config.pgd_steps
            )

            grad_metrics = measure_gradient_health(model, train_loader, config.device)

            # Local Lipschitz via block spectral norms
            spectral_metrics = measure_all_block_spectral_norms(model, train_loader, config.device)

            if aggregator != 'standard':
                agg_fn = model.blocks[0].attn.aggregate
                diagonal_gain = measure_diagonal_gain(agg_fn, config.d_model, n_samples=500, device=config.device)
                epoch_data['diagonal_gain'] = diagonal_gain

            epoch_data.update(rob_metrics)
            epoch_data.update(grad_metrics)
            epoch_data.update(spectral_metrics)

            print(f"\nEpoch {epoch+1} Summary:")
            print(f"  Train: {train_metrics['train_accuracy']:.4f}")
            print(f"  Test: {test_metrics['test_accuracy']:.4f}")
            print(f"  Clean: {rob_metrics['clean_accuracy']:.4f}")
            print(f"  Adversarial: {rob_metrics['adversarial_accuracy']:.4f}")
            print(f"  Gradient norm: {grad_metrics['grad_norm_mean']:.4f}")
            print(f"  Block spectral norm: {spectral_metrics['block_spectral_norm_mean']:.4f}")
            if 'diagonal_gain' in epoch_data:
                print(f"  Diagonal gain: {epoch_data['diagonal_gain']:.6f}")
            sys.stdout.flush()

        all_results.append(epoch_data)

        if test_metrics['test_accuracy'] > best_acc:
            best_acc = test_metrics['test_accuracy']
            best_model_state = {k: v.cpu() for k, v in model.state_dict().items()}
            print(f"  New best accuracy: {best_acc:.4f}")
            sys.stdout.flush()

    train_time = time.time() - start_time
    print(f"\nTraining complete. Time: {train_time:.1f}s")
    sys.stdout.flush()

    print("\nFinal evaluation:")
    sys.stdout.flush()
    model.load_state_dict({k: v.to(config.device) for k, v in best_model_state.items()})

    final_test = evaluate(model, test_loader, config.device)
    final_rob = evaluate_robustness(model, test_loader, config.device,
                                     config.pgd_epsilon, config.pgd_alpha, config.pgd_steps)
    final_grad = measure_gradient_health(model, train_loader, config.device)
    final_spectral = measure_all_block_spectral_norms(model, train_loader, config.device)

    if aggregator != 'standard':
        agg_fn = model.blocks[0].attn.aggregate
        final_diagonal_gain = measure_diagonal_gain(agg_fn, config.d_model, n_samples=1000, device=config.device)
        final_identity_error = measure_identity_error(agg_fn, config.d_model, n_samples=100, device=config.device)

        operator_metrics = {
            'final_diagonal_gain': final_diagonal_gain,
            'final_identity_error': final_identity_error,
        }
    else:
        operator_metrics = {}

    print(f"\nFinal Results:")
    print(f"  Clean accuracy: {final_rob['clean_accuracy']:.4f}")
    print(f"  Adversarial accuracy: {final_rob['adversarial_accuracy']:.4f}")
    print(f"  Gradient norm: {final_grad['grad_norm_mean']:.4f}")
    print(f"  Block spectral norm: {final_spectral['block_spectral_norm_mean']:.4f}")
    if operator_metrics:
        print(f"  Diagonal gain: {operator_metrics['final_diagonal_gain']:.6f}")
        print(f"  Identity error: {operator_metrics['final_identity_error']:.6f}")
    sys.stdout.flush()

    results = {
        'aggregator': aggregator,
        'config': asdict(config),
        'n_parameters': n_params,
        'training_time_seconds': train_time,
        'pre_training_metrics': pre_metrics,
        'final_metrics': {
            **final_test,
            **final_rob,
            **final_grad,
            **final_spectral,
            **operator_metrics,
        },
        'training_history': all_results,
    }

    return results


def main():
    """Run all experiments."""
    config = Config()
    print(f"\nExperiment configuration:")
    print(f"  Device: {config.device}")
    print(f"  Batch size: {config.batch_size}")
    print(f"  Epochs: {config.epochs}")
    print(f"  Learning rate: {config.lr}")
    sys.stdout.flush()

    aggregators = [
        'affine_d2',
        'affine_d3',
        'median_soft',
        'median_hard',
        'standard',
    ]

    all_results = {}

    for agg in aggregators:
        try:
            results = run_single_experiment(agg, config)
            all_results[agg] = results

            output_path = Path('triadic_stability_results.json')
            print(f"\nSaving results to {output_path}...", flush=True)
            with open(output_path, 'w') as f:
                json.dump(all_results, f, indent=2)

            print(f"Results saved ({output_path.stat().st_size / 1024:.1f} KB)")
            sys.stdout.flush()

        except Exception as e:
            print(f"\nERROR in {agg}: {e}")
            import traceback
            traceback.print_exc()
            sys.stdout.flush()
            continue

    print("\n" + "="*80)
    print("Summary")
    print("="*80)
    print(f"{'Aggregator':<15} {'L_D':<8} {'SpecNorm':<10} {'Clean':<8} {'Adv':<8} {'Grad':<8}")
    print("-"*80)

    for agg, res in all_results.items():
        fm = res['final_metrics']
        diag_gain = fm.get('final_diagonal_gain', float('nan'))
        spec_norm = fm.get('block_spectral_norm_mean', float('nan'))
        clean = fm['clean_accuracy']
        adv = fm['adversarial_accuracy']
        grad_norm = fm['grad_norm_mean']

        print(f"{agg:<15} {diag_gain:<8.4f} {spec_norm:<10.4f} {clean:<8.4f} {adv:<8.4f} {grad_norm:<8.4f}")

    print("\nExpected from PCTA.v:")
    print("  affine_d2: L_D (diagonal gain) = 1.5")
    print("  affine_d3, median_*: L_D = 1.0")
    print("  SpecNorm: local Lipschitz of residual blocks (should correlate with stability)")

    output_path = Path('triadic_stability_results.json')
    print(f"\nComplete results: {output_path} ({output_path.stat().st_size / 1024:.1f} KB)")
    sys.stdout.flush()


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"\nFATAL ERROR: {e}")
        import traceback
        traceback.print_exc()
        sys.stdout.flush()
        sys.exit(1)
