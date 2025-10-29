import numpy as np
import sys
from scipy import stats, linalg, optimize
from decimal import Decimal, getcontext

print("=" * 70)
print("PCTA VALIDATION SUITE")
print("=" * 70)
print()

# TEST 1: CORE PROOF VALIDATION
print("TEST 1: Core Proof Validation")
print("-" * 70)

def ternary_op(x):
    return (x + x + x) / 2

# 1.1 Multiple precision verification
print("1.1 Arbitrary precision verification:")
getcontext().prec = 50

def ternary_op_decimal(x):
    return (x + x + x) / Decimal(2)

for x0_float in [1.0, 0.001, 1000.0]:
    x_float = x0_float
    x_decimal = Decimal(str(x0_float))

    for i in range(12):
        x_float = ternary_op(x_float)
        x_decimal = ternary_op_decimal(x_decimal)

    expected = Decimal(str(x0_float)) * (Decimal(3) / Decimal(2)) ** 12
    float_error = abs(float(x_decimal) - x_float) / abs(float(x_decimal))
    decimal_error = abs(x_decimal - expected) / abs(expected)

    print(f"  x0={x0_float:8.3f}: float_err={float_error:.2e}, decimal_err={float(decimal_error):.2e}")

# 1.2 Initial condition sweep
print("\n1.2 Initial condition sweep:")
x0_values = np.logspace(-10, 10, 21)
errors = []

for x0 in x0_values:
    x = x0
    for i in range(12):
        x = ternary_op(x)
    expected = x0 * (3/2)**12
    rel_error = abs(x - expected) / abs(expected) if expected != 0 else abs(x)
    errors.append(rel_error)

print(f"  Range: [{x0_values[0]:.2e}, {x0_values[-1]:.2e}]")
print(f"  Max error: {max(errors):.2e}, Mean: {np.mean(errors):.2e}, Median: {np.median(errors):.2e}")

# 1.3 Lipschitz constant
print("\n1.3 Lipschitz constant:")
np.random.seed(42)
lipschitz_samples = []

for _ in range(1000):
    x = np.random.uniform(-100, 100)
    y = np.random.uniform(-100, 100)
    if abs(x - y) > 1e-10:
        Tx = ternary_op(x)
        Ty = ternary_op(y)
        L = abs(Tx - Ty) / abs(x - y)
        lipschitz_samples.append(L)

print(f"  Mean: {np.mean(lipschitz_samples):.10f}")
print(f"  Std: {np.std(lipschitz_samples):.10e}")
print(f"  Min: {min(lipschitz_samples):.10f}, Max: {max(lipschitz_samples):.10f}")

# 1.4 Jacobian verification
print("\n1.4 Jacobian analysis:")
test_points = [-10, -1, 0, 1, 10]
for x in test_points:
    h = 1e-8
    numerical_derivative = (ternary_op(x + h) - ternary_op(x - h)) / (2 * h)
    analytical_derivative = 1.5
    error = abs(numerical_derivative - analytical_derivative)
    print(f"  x={x:6.1f}: numerical={numerical_derivative:.10f}, analytical=1.5000000000, err={error:.2e}")

# 1.5 Conditioning analysis
print("\n1.5 Numerical conditioning:")
for n_iter in [1, 5, 10, 12, 15]:
    x = 1.0
    for i in range(n_iter):
        x = ternary_op(x)
    condition = 1.5 ** n_iter
    print(f"  After {n_iter:2d} iterations: value={x:.6e}, condition_number={condition:.6e}")

print()

# TEST 2: NUMERICAL PDE STABILITY
print("TEST 2: Numerical PDE Stability")
print("-" * 70)

def heat_step_d2(u):
    return (np.roll(u, 1) + u + np.roll(u, -1)) / 2

def heat_step_d4(u):
    return (np.roll(u, 1) + 2*u + np.roll(u, -1)) / 4

# 2.1 Spectral analysis
print("2.1 Spectral analysis:")
N = 64
for d in [2, 3, 4, 5]:
    c = d - 2
    A = np.zeros((N, N))
    for i in range(N):
        A[i, i] = c / d
        A[i, (i+1) % N] = 1 / d
        A[i, (i-1) % N] = 1 / d

    eigenvalues = linalg.eigvals(A)
    spectral_radius = max(abs(eigenvalues))
    print(f"  d={d}: spectral_radius={spectral_radius:.10f}, stable={spectral_radius <= 1.0}")

# 2.2 Von Neumann stability
print("\n2.2 Von Neumann stability:")
k_dense = np.linspace(0, np.pi, 1000)

for d in [2, 3, 4]:
    c = d - 2
    amplification = np.abs((2 * np.cos(k_dense) + c) / d)
    max_amp = np.max(amplification)
    mean_amp = np.mean(amplification)
    print(f"  d={d}: max|g(k)|={max_amp:.10f}, mean|g(k)|={mean_amp:.10f}")

# 2.3 Conservation properties
print("\n2.3 Conservation properties:")

def compute_moments(u):
    return {
        'L1': np.sum(np.abs(u)),
        'L2': np.sqrt(np.sum(u**2)),
        'Linf': np.max(np.abs(u)),
        'mass': np.sum(u),
    }

N = 100
u_d2_init = np.zeros(N)
u_d2_init[N//2] = 1.0
u_d4_init = u_d2_init.copy()

moments_d2_init = compute_moments(u_d2_init)
moments_d4_init = compute_moments(u_d4_init)

u_d2 = u_d2_init.copy()
u_d4 = u_d4_init.copy()

for _ in range(20):
    u_d2 = heat_step_d2(u_d2)
    u_d4 = heat_step_d4(u_d4)

moments_d2_final = compute_moments(u_d2)
moments_d4_final = compute_moments(u_d4)

print("  d=2:")
for key in ['L1', 'L2', 'Linf', 'mass']:
    ratio = moments_d2_final[key] / moments_d2_init[key]
    print(f"    {key:4s}: ratio={ratio:10.2f}")

print("  d=4:")
for key in ['L1', 'L2', 'Linf', 'mass']:
    ratio = moments_d4_final[key] / moments_d4_init[key]
    print(f"    {key:4s}: ratio={ratio:10.6f}")

print()

# TEST 3: FEDERATED LEARNING BYZANTINE RESILIENCE
print("TEST 3: Federated Learning Byzantine Resilience")
print("-" * 70)

def simple_average(values):
    return np.mean(values, axis=0)

def median_aggregate(values):
    return np.median(values, axis=0)

def krum(values, n_byzantine):
    n = len(values)
    if n <= 2 * n_byzantine:
        return np.median(values)
    scores = []
    for i in range(n):
        dists = sorted([abs(values[i] - values[j]) for j in range(n) if i != j])
        score = sum(dists[:n - n_byzantine - 1])
        scores.append(score)
    return values[np.argmin(scores)]

# 3.1 Aggregation comparison
print("3.1 Aggregation method comparison:")

aggregation_methods = [
    ("Average", lambda v: simple_average(v)),
    ("Median", lambda v: median_aggregate(v)),
    ("Krum(f=1)", lambda v: krum(v, 1)),
]

byzantine_attacks = [
    ("alternating ±1000", lambda r: 1000.0 if r % 2 == 0 else -1000.0),
    ("linear +1000*r", lambda r: 1000.0 * r),
]

for attack_name, attack_fn in byzantine_attacks:
    print(f"  Attack: {attack_name}")

    for agg_name, agg_fn in aggregation_methods:
        model_param = 1.0

        for round_num in range(12):
            honest_updates = [1.0, 1.0]
            byzantine_update = attack_fn(round_num)
            all_updates = honest_updates + [byzantine_update]
            aggregated = agg_fn(all_updates)
            model_param = model_param * aggregated

        stable = abs(model_param - 1.0) < 1e-3
        log_param = np.log10(abs(model_param)) if model_param != 0 else -np.inf
        print(f"    {agg_name:15s}: log10={log_param:7.2f}, stable={stable}")

# 3.2 Byzantine tolerance verification
print("\n3.2 Byzantine tolerance verification:")
configurations = [(3, 0), (4, 1), (6, 1), (6, 2), (9, 2), (9, 3)]

for n_honest, n_byz in configurations:
    n_total = n_honest + n_byz
    tolerance_bound = n_byz < n_total / 3

    model = 1.0
    for r in range(20):
        honest = [1.0] * n_honest
        byz = [1000.0 if r % 2 == 0 else -1000.0] * n_byz
        aggregated = median_aggregate(honest + byz)
        model *= aggregated

    empirically_stable = abs(model - 1.0) < 1e-6

    print(f"  n={n_total:2d} (h={n_honest}, b={n_byz}): f={n_byz/n_total:.3f}, theory={tolerance_bound}, empirical={empirically_stable}")

print()

# TEST 4: PRICE ORACLE ATTACK SIMULATION
print("TEST 4: Price Oracle Attack Simulation")
print("-" * 70)

# 4.1 Multi-exchange price aggregation
print("4.1 Multi-exchange price aggregation:")
np.random.seed(42)

true_price_base = 50000.0
n_exchanges = 5
n_timestamps = 100

print(f"  Exchanges: {n_exchanges}, timestamps: {n_timestamps}, base_price: ${true_price_base:,.2f}")

exchange_spreads = np.array([0.001, 0.0015, 0.0012, 0.0008, 0.0010])
exchange_latencies = np.array([10, 15, 8, 20, 12])

prices_honest = np.zeros((n_timestamps, n_exchanges))
volatility = 0.02

for t in range(n_timestamps):
    market_move = np.random.normal(0, volatility * true_price_base / np.sqrt(n_timestamps))
    true_price = true_price_base + market_move * t / n_timestamps

    for e in range(n_exchanges):
        spread = exchange_spreads[e] * true_price
        latency_factor = 1.0 - 0.0001 * exchange_latencies[e]
        noise = np.random.normal(0, spread / 3)
        prices_honest[t, e] = true_price * latency_factor + noise

print(f"  Price range: ${np.min(prices_honest):,.2f} - ${np.max(prices_honest):,.2f}")
print(f"  Mean spread: {np.mean(np.std(prices_honest, axis=1) / np.mean(prices_honest, axis=1)) * 100:.4f}%")

# 4.2 Byzantine price manipulation
print("\n4.2 Byzantine price manipulation:")

attack_scenarios = [
    ("10% inflation", lambda p: p * 1.10),
    ("50% inflation", lambda p: p * 1.50),
    ("100% inflation", lambda p: p * 2.00),
    ("90% deflation", lambda p: p * 0.10),
]

for attack_name, attack_fn in attack_scenarios:
    print(f"  Attack: {attack_name}")

    prices_attacked = prices_honest.copy()
    prices_attacked[:, 1] = attack_fn(prices_attacked[:, 1])

    financial_losses = []
    median_errors = []

    for t in range(n_timestamps):
        true_price = np.median(prices_honest[t, :])

        avg_price = np.mean(prices_attacked[t, :])
        avg_error = abs(avg_price - true_price) / true_price

        med_price = np.median(prices_attacked[t, :])
        med_error = abs(med_price - true_price) / true_price

        trade_volume = 1_000_000
        financial_losses.append(avg_error * trade_volume)
        median_errors.append(med_error)

    total_loss = sum(financial_losses)
    max_loss = max(financial_losses)
    median_max_error = max(median_errors)

    print(f"    Average: total_loss=${total_loss:,.2f}, max_loss=${max_loss:,.2f}")
    print(f"    Median:  max_error={median_max_error:.6f}")

# 4.3 Attack detection
print("\n4.3 Attack detection:")

prices_attacked = prices_honest.copy()
prices_attacked[:, 1] = prices_attacked[:, 1] * 1.50

thresholds = [0.01, 0.02, 0.05, 0.10]

for threshold in thresholds:
    detected = 0
    false_positives = 0

    for t in range(n_timestamps):
        median_price = np.median(prices_attacked[t, :])

        for e in range(n_exchanges):
            deviation = abs(prices_attacked[t, e] - median_price) / median_price

            if deviation > threshold:
                if e == 1:
                    detected += 1
                else:
                    false_positives += 1

    detection_rate = detected / n_timestamps
    fpr = false_positives / (n_timestamps * (n_exchanges - 1))

    print(f"  threshold={threshold:.2%}: detection={detection_rate:.2%}, false_positives={fpr:.2%}")

# 4.4 Multi-Byzantine collusion
print("\n4.4 Collusion attack:")

n_colluding = 2
prices_collusion = prices_honest.copy()

for attack_magnitude in [1.2, 1.5, 2.0]:
    prices_collusion[:, 0:n_colluding] = prices_honest[:, 0:n_colluding] * attack_magnitude

    losses = []
    for t in range(n_timestamps):
        true_price = np.median(prices_honest[t, :])
        avg_price = np.mean(prices_collusion[t, :])
        med_price = np.median(prices_collusion[t, :])

        avg_error = abs(avg_price - true_price) / true_price
        med_error = abs(med_price - true_price) / true_price

        losses.append((avg_error * 1_000_000, med_error * 1_000_000))

    avg_total = sum(l[0] for l in losses)
    med_total = sum(l[1] for l in losses)

    print(f"  {attack_magnitude:.1f}x: avg_loss=${avg_total:,.2f}, med_loss=${med_total:,.2f}, ratio={avg_total/med_total:.1f}x")

# 4.5 Temporal attack
print("\n4.5 Temporal attack:")

prices_gradual = prices_honest.copy()
for t in range(50, n_timestamps):
    attack_strength = 1.0 + 0.5 * (t - 50) / 50
    prices_gradual[t, 1] = prices_gradual[t, 1] * attack_strength

cumulative_avg_loss = 0
cumulative_med_loss = 0

detection_timestamp = None

for t in range(n_timestamps):
    true_price = np.median(prices_honest[t, :])
    avg_price = np.mean(prices_gradual[t, :])
    med_price = np.median(prices_gradual[t, :])

    avg_error = abs(avg_price - true_price)
    med_error = abs(med_price - true_price)

    cumulative_avg_loss += avg_error
    cumulative_med_loss += med_error

    if detection_timestamp is None and cumulative_avg_loss > 1000:
        detection_timestamp = t

print(f"  Attack starts: t=50")
print(f"  Detection: t={detection_timestamp}")
print(f"  Cumulative: avg=${cumulative_avg_loss:,.2f}, med=${cumulative_med_loss:,.2f}")

# 4.6 Arbitrage opportunity
print("\n4.6 Arbitrage opportunity:")

prices_arb = prices_honest.copy()
prices_arb[:, 1] = prices_arb[:, 1] * 0.90

arbitrage_profits = []

for t in range(n_timestamps):
    oracle_avg = np.mean(prices_arb[t, :])
    oracle_med = np.median(prices_arb[t, :])
    true_market = np.median(prices_honest[t, :])

    avg_arb = abs(oracle_avg - true_market)
    med_arb = abs(oracle_med - true_market)

    arbitrage_profits.append(avg_arb)

total_arb = sum(arbitrage_profits)
print(f"  Total mispricing: ${total_arb:,.2f}")
print(f"  Per-timestamp: ${np.mean(arbitrage_profits):,.2f}")
print(f"  Maximum: ${max(arbitrage_profits):,.2f}")

# 4.7 Industry scale
print("\n4.7 Industry scale:")

daily_defi_volume = 5_000_000_000
timestamps_per_day = 8640

loss_per_update = np.mean(financial_losses)
projected_daily_loss = loss_per_update * timestamps_per_day

print(f"  Daily volume: ${daily_defi_volume:,.0f}")
print(f"  Updates/day: {timestamps_per_day:,}")
print(f"  Loss/update: ${loss_per_update:,.2f}")
print(f"  Daily loss: ${projected_daily_loss:,.2f}")
print(f"  Annual: ${projected_daily_loss * 365:,.2f}")

# 4.8 Byzantine f-tolerance
print("\n4.8 Byzantine f-tolerance:")

for n in [3, 5, 7, 9, 11]:
    max_tolerable = (n - 1) // 3

    prices_boundary = np.ones((10, n)) * 50000
    for i in range(max_tolerable):
        prices_boundary[:, i] = prices_boundary[:, i] * 2.0

    median_price = np.median(prices_boundary[0, :])
    avg_price = np.mean(prices_boundary[0, :])

    median_stable = abs(median_price - 50000) / 50000 < 0.01
    avg_stable = abs(avg_price - 50000) / 50000 < 0.01

    print(f"  n={n:2d}: f_max={max_tolerable}, median_stable={median_stable}, avg_stable={avg_stable}")

print()
print("=" * 70)
print("END OF VALIDATION SUITE")
print("=" * 70)
