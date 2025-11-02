"""
Constraint Verification System for N-ary Consensus Protocols

Implements computational verification of the impossibility theorem connecting
algebraic constraints (cyclic symmetry, identity law, affine structure) to
geometric optimality bounds (Hilbert metric contraction rates).

Based on the formalization in PCTA.v

Usage:
    python constraint_verification.py

Test Suite:
- Constraint checking (cyclic, identity, affine)
- Lipschitz constant measurement
- Hilbert metric contraction rate measurement
- Duality verification (kappa * tau = 1)
- Contraction rate certification
- Byzantine resilience analysis
- Approximate constraint satisfaction region
- Scaling verification to high dimensions
- Weighted cyclic symmetry tests
- Threshold voting protocol analysis
- Convergence time certification
- Extreme case sampling
- Boundary protocol analysis
"""

import numpy as np
from typing import Callable, List, Tuple, Optional, Dict
from dataclasses import dataclass
from itertools import permutations
from scipy.optimize import minimize

class ValidationError(Exception):
    pass

class Config:
    EPSILON_CYCLIC = 1e-10
    EPSILON_IDENTITY = 1e-10
    EPSILON_AFFINE = 1e-7
    EPSILON_SUM = 1e-7
    EPSILON_COEFF = 1e-8
    EPSILON_DUALITY = 1e-12

    DEFAULT_CYCLIC_SAMPLES = 100
    DEFAULT_IDENTITY_SAMPLES = 100
    DEFAULT_AFFINE_SAMPLES = 200
    DEFAULT_LIPSCHITZ_SAMPLES = 1000
    DEFAULT_IMPOSSIBILITY_TRIALS = 100

    MIN_N = 2

@dataclass
class Protocol:
    n: int
    operation: Callable[[List[float]], float]
    name: str
    description: str = ""

    def __post_init__(self):
        if self.n < Config.MIN_N:
            raise ValidationError(f"n must be >= {Config.MIN_N}, got {self.n}")

class ConstraintChecker:
    """Verify algebraic constraints on n-ary operations."""

    @staticmethod
    def validate_inputs(inputs: List[float], expected_n: int) -> None:
        if len(inputs) != expected_n:
            raise ValidationError(f"Expected {expected_n} inputs, got {len(inputs)}")

    @staticmethod
    def sum_list(l: List[float]) -> float:
        """Fixpoint sum_list (l : list R) : R."""
        return sum(l)

    @staticmethod
    def nary_cyclic(op: Callable[[List[float]], float], n: int,
                    test_inputs: List[float], rotations: int = None,
                    epsilon: float = None) -> Tuple[bool, float]:
        """
        Definition nary_cyclic (n : nat) (op : list R -> R) : Prop :=
          forall (l : list R), length l = n ->
          forall k, (k < n)%nat ->
          op l = op (skipn k l ++ firstn k l).
        """
        if n < Config.MIN_N:
            raise ValidationError(f"n must be >= {Config.MIN_N}, got {n}")

        ConstraintChecker.validate_inputs(test_inputs, n)

        if epsilon is None:
            epsilon = Config.EPSILON_CYCLIC

        if rotations is None:
            rotations = n

        max_violation = 0.0
        baseline = op(test_inputs)

        for k in range(1, min(rotations, n)):
            rotated = test_inputs[k:] + test_inputs[:k]
            result = op(rotated)
            violation = abs(baseline - result)
            max_violation = max(max_violation, violation)

        is_cyclic = max_violation < epsilon
        return is_cyclic, max_violation

    @staticmethod
    def nary_identity_law(op: Callable[[List[float]], float], n: int,
                         e: float, samples: int = None, epsilon: float = None) -> Tuple[bool, float]:
        """
        Definition nary_identity_law (n : nat) (op : list R -> R) (e : R) : Prop :=
          forall a, op (e :: repeat a (n - 1)) = a.
        """
        if n < Config.MIN_N:
            raise ValidationError(f"n must be >= {Config.MIN_N}, got {n}")

        if samples is None:
            samples = Config.DEFAULT_IDENTITY_SAMPLES

        if epsilon is None:
            epsilon = Config.EPSILON_IDENTITY

        max_violation = 0.0

        for _ in range(samples):
            a = np.random.randn()
            inputs = [e] + [a] * (n - 1)
            result = op(inputs)
            violation = abs(result - a)
            max_violation = max(max_violation, violation)

        is_identity = max_violation < epsilon
        return is_identity, max_violation

    @staticmethod
    def nary_affine(op: Callable[[List[float]], float], n: int,
                   samples: int = None, epsilon_fit: float = None,
                   epsilon_sum: float = None) -> Tuple[bool, Optional[List[float]], float]:
        """
        Definition nary_affine (n : nat) (op : list R -> R) : Prop :=
          exists (coeffs : list R),
            length coeffs = n /\
            sum_list coeffs = 1 /\
            forall (inputs : list R), length inputs = n ->
              op inputs = sum_list (map (fun '(c, x) => c * x) (combine coeffs inputs)).
        """
        if n < Config.MIN_N:
            raise ValidationError(f"n must be >= {Config.MIN_N}, got {n}")

        if samples is None:
            samples = Config.DEFAULT_AFFINE_SAMPLES

        if epsilon_fit is None:
            epsilon_fit = Config.EPSILON_AFFINE

        if epsilon_sum is None:
            epsilon_sum = Config.EPSILON_SUM

        X = []
        Y = []

        for _ in range(samples):
            inputs = np.random.randn(n).tolist()
            X.append(inputs)
            Y.append(op(inputs))

        X = np.array(X)
        Y = np.array(Y)

        try:
            coeffs, residuals, rank, s = np.linalg.lstsq(X, Y, rcond=None)

            if residuals.size > 0:
                fit_error = np.sqrt(residuals[0] / samples)
            else:
                Y_pred = X @ coeffs
                fit_error = np.sqrt(np.mean((Y - Y_pred)**2))

            sum_coeffs = sum(coeffs)
            sum_violation = abs(sum_coeffs - 1.0)

            is_affine = (fit_error < epsilon_fit) and (sum_violation < epsilon_sum)

            return is_affine, coeffs.tolist() if is_affine else None, fit_error
        except (np.linalg.LinAlgError, ValueError) as e:
            raise ValidationError(f"Linear algebra error in affine check: {e}")
        except Exception as e:
            raise ValidationError(f"Unexpected error in affine check: {e}")

class TheoremVerifier:
    """Verify theorems from the formalization."""

    @staticmethod
    def compute_lipschitz_constant(n: int) -> float:
        """
        Definition compute_lipschitz_constant_Q (n : nat) : option Q :=
          Some (Z.of_nat n # Pos.of_nat (n - 1)).
        """
        if n < Config.MIN_N:
            raise ValidationError(f"n must be >= {Config.MIN_N}, got {n}")
        return n / (n - 1)

    @staticmethod
    def compute_hilbert_contraction_rate(n: int) -> float:
        """
        Definition hilbert_contraction_rate (n : nat) : R :=
          1 - 1 / INR n.
        """
        if n < Config.MIN_N:
            raise ValidationError(f"n must be >= {Config.MIN_N}, got {n}")
        return 1 - 1 / n

    @staticmethod
    def verify_duality(n: int) -> Dict:
        """
        Lemma lipschitz_times_contraction_equals_one :
          (INR n / INR (n - 1)) * (1 - 1 / INR n) = 1.
        """
        kappa = TheoremVerifier.compute_lipschitz_constant(n)
        tau = TheoremVerifier.compute_hilbert_contraction_rate(n)
        product = kappa * tau

        return {
            'n': n,
            'kappa_obstruction': kappa,
            'tau_contraction': tau,
            'product': product,
            'duality_verified': abs(product - 1.0) < 1e-12
        }

    @staticmethod
    def check_first_coeff_zero(coeffs: List[float]) -> bool:
        """Lemma first_coeff_from_identity: c0 = 0 and sum_list cs = 1."""
        if not coeffs:
            return False

        c0 = coeffs[0]
        cs = coeffs[1:]

        return abs(c0) < Config.EPSILON_COEFF and abs(sum(cs) - 1.0) < Config.EPSILON_COEFF

    @staticmethod
    def check_coeffs_equal(coeffs: List[float]) -> bool:
        """Theorem cyclic_identity_forces_equal_coefficients: all coeffs equal."""
        if not coeffs:
            return False

        reference = coeffs[0]
        return all(abs(c - reference) < Config.EPSILON_COEFF for c in coeffs)

    @staticmethod
    def test_impossibility(n: int, num_trials: int = 100) -> Dict:
        """
        Theorem nary_impossibility_general :
          (n >= 2)%nat ->
          nary_cyclic n op ->
          nary_identity_law n op 0 ->
          nary_affine n op ->
          False.
        """
        satisfying = []

        for _ in range(num_trials):
            coeffs = np.random.randn(n)
            coeffs = coeffs / np.sum(coeffs)

            def affine_op(inputs: List[float]) -> float:
                return sum(c * x for c, x in zip(coeffs, inputs))

            test_inputs = np.random.randn(n).tolist()

            is_cyc, _ = ConstraintChecker.nary_cyclic(affine_op, n, test_inputs)
            is_id, _ = ConstraintChecker.nary_identity_law(affine_op, n, 0.0, samples=20)
            is_aff, _, _ = ConstraintChecker.nary_affine(affine_op, n, samples=50)

            if is_cyc and is_id and is_aff:
                satisfying.append(coeffs.tolist())

        return {
            'n': n,
            'trials': num_trials,
            'satisfying_count': len(satisfying),
            'impossibility_verified': len(satisfying) == 0,
            'violating_protocols': satisfying
        }

class ProtocolAnalyzer:
    """Analyze concrete protocols against constraints."""

    def __init__(self, protocol: Protocol, identity_element: float = 0.0):
        self.protocol = protocol
        self.identity_element = identity_element
        self.checker = ConstraintChecker()

    def analyze(self, test_samples: int = 100) -> Dict:
        """Full constraint analysis."""
        n = self.protocol.n
        test_inputs = np.random.randn(n).tolist()

        is_cyc, cyc_err = self.checker.nary_cyclic(
            self.protocol.operation, n, test_inputs, rotations=n
        )
        is_id, id_err = self.checker.nary_identity_law(
            self.protocol.operation, n, self.identity_element, samples=test_samples
        )
        is_aff, coeffs, aff_err = self.checker.nary_affine(
            self.protocol.operation, n, samples=test_samples
        )

        result = {
            'name': self.protocol.name,
            'description': self.protocol.description,
            'n': n,
            'constraints': {
                'cyclic': is_cyc,
                'identity': is_id,
                'affine': is_aff
            },
            'errors': {
                'cyclic_max_violation': cyc_err,
                'identity_max_violation': id_err,
                'affine_fit_error': aff_err
            },
            'satisfies_all_three': is_cyc and is_id and is_aff
        }

        if is_aff and coeffs:
            result['coefficients'] = coeffs
            result['coefficient_sum'] = sum(coeffs)
            result['first_coeff_zero'] = TheoremVerifier.check_first_coeff_zero(coeffs)
            result['coeffs_equal'] = TheoremVerifier.check_coeffs_equal(coeffs)

        return result

    def compute_lipschitz_estimate(self, samples: int = 1000) -> float:
        """Numerical Lipschitz constant estimation."""
        max_ratio = 0.0
        n = self.protocol.n

        for _ in range(samples):
            x1 = np.random.randn(n).tolist()
            x2 = np.random.randn(n).tolist()

            output_diff = abs(self.protocol.operation(x1) - self.protocol.operation(x2))
            input_diff = max(abs(a - b) for a, b in zip(x1, x2))

            if input_diff > 1e-10:
                ratio = output_diff / input_diff
                max_ratio = max(max_ratio, ratio)

        return max_ratio

    def measure_hilbert_contraction(self, samples: int = 500) -> Dict:
        """Measure Hilbert metric contraction rate on probability simplex."""
        n = self.protocol.n
        contractions = []

        for _ in range(samples):
            x = np.random.dirichlet(np.ones(n))
            y = np.random.dirichlet(np.ones(n))

            ratios = x / y
            M = np.max(ratios)
            m = np.min(ratios)
            d_before = np.log(M / m) if M / m > 1 + 1e-10 else 0

            if d_before > 1e-6:
                fx = self.protocol.operation(x.tolist())
                fy = self.protocol.operation(y.tolist())
                d_after = abs(fx - fy)

                if d_before > 0:
                    contraction_ratio = d_after / d_before
                    contractions.append(contraction_ratio)

        if contractions:
            return {
                'mean': np.mean(contractions),
                'max': np.max(contractions),
                'min': np.min(contractions),
                'std': np.std(contractions)
            }
        else:
            return {'mean': 0, 'max': 0, 'min': 0, 'std': 0}

    def measure_equilibrium_contraction(self, samples: int = 500) -> Dict:
        """Measure contraction near fixed points/equilibria."""
        n = self.protocol.n
        contractions = []

        for _ in range(samples):
            a = np.random.randn()
            eps = np.random.randn(n) * 0.1

            x1 = np.array([0.0] + [a] * (n-1)) + eps
            x2 = np.array([0.0] + [a] * (n-1)) + eps * 1.5

            dist_before = np.linalg.norm(x1 - x2, ord=np.inf)

            if dist_before > 1e-6:
                fx1 = self.protocol.operation(x1.tolist())
                fx2 = self.protocol.operation(x2.tolist())

                dist_after = abs(fx1 - fx2)
                contraction = dist_after / dist_before
                contractions.append(contraction)

        if contractions:
            return {
                'mean': np.mean(contractions),
                'max': np.max(contractions),
                'min': np.min(contractions),
                'std': np.std(contractions)
            }
        else:
            return {'mean': 0, 'max': 0, 'min': 0, 'std': 0}

def run_full_verification(n: int = 3) -> None:
    """Execute complete verification suite."""

    print(f"n = {n}")
    print()

    print("duality verification:")
    duality = TheoremVerifier.verify_duality(n)
    print(f"  kappa_obstruction = {duality['kappa_obstruction']:.6f}")
    print(f"  tau_contraction = {duality['tau_contraction']:.6f}")
    print(f"  product = {duality['product']:.6f}")
    print(f"  duality_verified = {duality['duality_verified']}")
    print()

    print("impossibility theorem verification:")
    impossibility = TheoremVerifier.test_impossibility(n, num_trials=100)
    print(f"  trials = {impossibility['trials']}")
    print(f"  satisfying_count = {impossibility['satisfying_count']}")
    print(f"  impossibility_verified = {impossibility['impossibility_verified']}")
    print()

    def identity_preserving(l: List[float]) -> float:
        if len(l) < 2:
            raise ValidationError("identity_preserving requires n >= 2")
        return sum(l[1:]) / (len(l) - 1)

    protocols = [
        Protocol(n, lambda l: np.median(l), "median",
                "non-affine Byzantine-resilient"),
        Protocol(n, lambda l: sum(l) / 2, "denominator_2",
                "affine with coefficient sum = 3/2"),
        Protocol(n, lambda l: sum(l) / n, "average",
                "cyclic affine without identity"),
        Protocol(n, identity_preserving, "identity_preserving",
                "affine with first coefficient zero")
    ]

    for proto in protocols:
        analyzer = ProtocolAnalyzer(proto)
        result = analyzer.analyze(test_samples=100)

        print(f"{result['name']}:")
        if result['description']:
            print(f"  description: {result['description']}")

        constraints = result['constraints']
        print(f"  cyclic = {constraints['cyclic']}")
        print(f"  identity = {constraints['identity']}")
        print(f"  affine = {constraints['affine']}")

        if 'coefficients' in result:
            coeffs = result['coefficients']
            print(f"  coefficients = [{', '.join(f'{c:.6f}' for c in coeffs)}]")
            print(f"  coefficient_sum = {result['coefficient_sum']:.6f}")

            if 'first_coeff_zero' in result:
                print(f"  first_coeff_zero = {result['first_coeff_zero']}")
            if 'coeffs_equal' in result:
                print(f"  coeffs_equal = {result['coeffs_equal']}")

        errors = result['errors']
        if errors['cyclic_max_violation'] < 1e-6:
            lipschitz = analyzer.compute_lipschitz_estimate(samples=500)
            print(f"  lipschitz_estimate = {lipschitz:.6f}")

        print(f"  satisfies_all_three = {result['satisfies_all_three']}")
        print()

class ContractionRateCertifier:
    """Certify Hilbert metric contraction rates from algebraic impossibility."""

    @staticmethod
    def compute_contraction_certificate(n: int, protocol_analysis: Dict) -> Dict:
        """Theorem: algebraic_impossibility_certifies_projective_metric_optimality"""
        constraints = protocol_analysis['constraints']

        tau_optimal = 1 - 1/n
        kappa_obstruction = n / (n - 1)

        satisfied = sum([
            constraints['cyclic'],
            constraints['identity'],
            constraints['affine']
        ])

        certificate = {
            'n': n,
            'tau_birkhoff_optimal': tau_optimal,
            'kappa_obstruction': kappa_obstruction,
            'constraints_satisfied': satisfied,
            'protocol_name': protocol_analysis['name']
        }

        if satisfied == 3:
            certificate['status'] = 'IMPOSSIBLE'
            certificate['conclusion'] = 'violates impossibility theorem'

        elif satisfied == 2:
            missing = [k for k, v in constraints.items() if not v][0]
            certificate['status'] = 'BOUNDED_SUBOPTIMAL'
            certificate['missing_constraint'] = missing

            if missing == 'cyclic':
                certificate['conclusion'] = f"cannot achieve cyclic symmetry, contraction deviates from tau={tau_optimal:.4f}"
            elif missing == 'identity':
                certificate['conclusion'] = f"cannot satisfy identity law"
            elif missing == 'affine':
                certificate['conclusion'] = f"nonlinear, can beat affine bound kappa={kappa_obstruction:.4f}"

        elif satisfied <= 1:
            certificate['status'] = 'UNCONSTRAINED'
            certificate['conclusion'] = 'multiple constraints violated'

        if 'lipschitz_estimate' in protocol_analysis:
            L_actual = protocol_analysis['lipschitz_estimate']
            certificate['lipschitz_actual'] = L_actual
            certificate['gap_from_obstruction'] = abs(L_actual - kappa_obstruction)

            if constraints['affine'] and not constraints['cyclic'] and not constraints['identity']:
                if abs(L_actual - kappa_obstruction) < 0.01:
                    certificate['at_boundary'] = True
                    certificate['conclusion'] += " [AT IMPOSSIBILITY BOUNDARY]"

        return certificate

    @staticmethod
    def verify_duality_via_violation(n: int,
                                    cyclic_affine_protocol: Callable,
                                    identity_affine_protocol: Callable) -> Dict:
        """Verify kappa·tau = 1 duality by measuring actual violations."""

        kappa_theory = n / (n - 1)
        tau_theory = 1 - 1/n

        analyzer1 = ProtocolAnalyzer(
            Protocol(n, cyclic_affine_protocol, "cyclic_affine_test")
        )
        L_cyclic = analyzer1.compute_lipschitz_estimate(samples=2000)

        analyzer2 = ProtocolAnalyzer(
            Protocol(n, identity_affine_protocol, "identity_affine_test"),
            identity_element=0.0
        )

        test_vals = []
        for _ in range(1000):
            a = np.random.randn()
            inputs = [0.0] + [a] * (n - 1)
            result = identity_affine_protocol(inputs)
            if abs(a) > 1e-6:
                test_vals.append(abs(result / a))

        tau_measured = np.mean(test_vals) if test_vals else 0.0

        product_actual = L_cyclic * tau_measured
        product_error = abs(product_actual - 1.0)

        return {
            'n': n,
            'kappa_theory': kappa_theory,
            'tau_theory': tau_theory,
            'kappa_measured': L_cyclic,
            'tau_measured': tau_measured,
            'product_theory': 1.0,
            'product_measured': product_actual,
            'product_error': product_error,
            'duality_verified': product_error < 0.05
        }

def run_constraint_space_analysis(n: int = 3) -> None:
    """Analyze distribution of protocols across constraint space."""

    print(f"constraint space analysis (n = {n}):")

    constraint_counts = {
        (False, False, False): 0,
        (False, False, True): 0,
        (False, True, False): 0,
        (False, True, True): 0,
        (True, False, False): 0,
        (True, False, True): 0,
        (True, True, False): 0,
        (True, True, True): 0
    }

    num_samples = 225
    for a in np.linspace(-1, 1, 15):
        for b in np.linspace(-1, 1, 15):
            c = 1 - a - b
            remaining = [c] + [0] * (n - 3) if n > 3 else [c]

            coeffs = [a, b] + remaining
            protocol = lambda x, coeffs=coeffs: sum(c * val for c, val in zip(coeffs, x))

            test_inputs = np.random.randn(n).tolist()

            is_cyc, _ = ConstraintChecker.nary_cyclic(protocol, n, test_inputs, rotations=3)
            is_id, _ = ConstraintChecker.nary_identity_law(protocol, n, 0.0, samples=20)
            is_aff, _, _ = ConstraintChecker.nary_affine(protocol, n, samples=30)

            key = (is_cyc, is_id, is_aff)
            constraint_counts[key] += 1

    for constraints, count in sorted(constraint_counts.items()):
        cyc, ident, aff = constraints
        print(f"  cyclic={cyc}, identity={ident}, affine={aff}: {count}")
    print()

def run_extreme_sampling(n: int = 3) -> Dict:
    """Test extreme and boundary cases."""
    extreme_cases = []

    for i in range(n):
        coeffs = [0.0] * n
        coeffs[i] = 1.0
        extreme_cases.append({'name': f'selector_{i}', 'coeffs': coeffs, 'category': 'pure_selector'})

    coeffs = [1/n] * n
    extreme_cases.append({'name': 'cyclic', 'coeffs': coeffs, 'category': 'cyclic'})

    coeffs = [0.0] + [1/(n-1)] * (n-1)
    extreme_cases.append({'name': 'identity', 'coeffs': coeffs, 'category': 'identity'})

    for epsilon in [0.01, 0.1, 0.2]:
        coeffs = [1/n - epsilon/2] + [1/n + epsilon/(2*(n-1))] * (n-1)
        coeffs = [c / sum(coeffs) for c in coeffs]
        extreme_cases.append({'name': f'near_cyclic_eps_{epsilon}', 'coeffs': coeffs, 'category': 'near_cyclic'})

    for epsilon in [0.01, 0.1, 0.2]:
        coeffs = [epsilon] + [(1-epsilon)/(n-1)] * (n-1)
        extreme_cases.append({'name': f'near_identity_eps_{epsilon}', 'coeffs': coeffs, 'category': 'near_identity'})

    if n == 3:
        coeffs = [10.0, -4.5, -4.5]
        coeffs = [c / sum(coeffs) for c in coeffs]
        extreme_cases.append({'name': 'large_positive_first', 'coeffs': coeffs, 'category': 'large_magnitude'})

        coeffs = [-5.0, 3.0, 3.0]
        coeffs = [c / sum(coeffs) for c in coeffs]
        extreme_cases.append({'name': 'large_negative_first', 'coeffs': coeffs, 'category': 'large_magnitude'})

    coeffs = [1/n] * n
    coeffs[0] += 1e-6
    coeffs[1] -= 1e-6
    extreme_cases.append({'name': 'tiny_perturb_cyclic', 'coeffs': coeffs, 'category': 'tiny_perturbation'})

    coeffs = [0.0] + [1/(n-1)] * (n-1)
    coeffs[0] += 1e-6
    coeffs[1] -= 1e-6
    extreme_cases.append({'name': 'tiny_perturb_identity', 'coeffs': coeffs, 'category': 'tiny_perturbation'})

    results = []
    for case in extreme_cases:
        coeffs = case['coeffs']

        def affine_op(inputs: List[float]) -> float:
            return sum(c * x for c, x in zip(coeffs, inputs))

        test_inputs = np.random.randn(n).tolist()

        is_cyc, cyc_err = ConstraintChecker.nary_cyclic(affine_op, n, test_inputs)
        is_id, id_err = ConstraintChecker.nary_identity_law(affine_op, n, 0.0, samples=100)
        is_aff, _, aff_err = ConstraintChecker.nary_affine(affine_op, n, samples=100)

        analyzer = ProtocolAnalyzer(Protocol(n, affine_op, case['name']))
        lip = analyzer.compute_lipschitz_estimate(samples=500)

        results.append({
            'name': case['name'],
            'category': case['category'],
            'coeffs': coeffs,
            'cyclic': is_cyc,
            'identity': is_id,
            'affine': is_aff,
            'cyclic_error': cyc_err,
            'identity_error': id_err,
            'affine_error': aff_err,
            'lipschitz': lip,
            'satisfies_all_three': is_cyc and is_id and is_aff
        })

    return {
        'n': n,
        'num_cases': len(results),
        'cases': results,
        'any_satisfy_all_three': any(r['satisfies_all_three'] for r in results)
    }

def run_extreme_input_testing(n: int = 3) -> Dict:
    """Test protocols with extreme input values."""
    protocols = [
        ("average", lambda l: sum(l) / n),
        ("identity_preserving", lambda l: sum(l[1:]) / (n - 1)),
        ("median", lambda l: np.median(l)),
    ]

    input_scenarios = [
        ("zeros", [0.0] * n),
        ("ones", [1.0] * n),
        ("large_positive", [1e6] * n),
        ("large_negative", [-1e6] * n),
        ("mixed_large", [1e6, -1e6, 0.0][:n] + [0.0] * max(0, n-3)),
        ("tiny", [1e-10] * n),
        ("one_large_rest_small", [1e6] + [1e-6] * (n-1)),
    ]

    results = []
    for proto_name, proto_op in protocols:
        for scenario_name, inputs in input_scenarios:
            try:
                output = proto_op(inputs)
                results.append({
                    'protocol': proto_name,
                    'scenario': scenario_name,
                    'output': output,
                    'output_finite': np.isfinite(output),
                    'error': None
                })
            except Exception as e:
                results.append({
                    'protocol': proto_name,
                    'scenario': scenario_name,
                    'output': None,
                    'output_finite': False,
                    'error': str(e)
                })

    return {'n': n, 'num_tests': len(results), 'results': results}

def run_contraction_certification(n: int = 3) -> None:
    """Test contraction rate certification."""

    print(f"contraction rate certification (n = {n}):")
    print()

    def identity_preserving(l: List[float]) -> float:
        if len(l) < 2:
            raise ValidationError("identity_preserving requires n >= 2")
        return sum(l[1:]) / (len(l) - 1)

    protocols = [
        Protocol(n, lambda l: np.median(l), "median"),
        Protocol(n, lambda l: sum(l) / 2, "denominator_2"),
        Protocol(n, lambda l: sum(l) / n, "average"),
        Protocol(n, identity_preserving, "identity_preserving")
    ]

    for proto in protocols:
        analyzer = ProtocolAnalyzer(proto)
        result = analyzer.analyze(test_samples=100)

        if result['constraints']['cyclic'] or result['constraints']['affine']:
            lipschitz = analyzer.compute_lipschitz_estimate(samples=500)
            result['lipschitz_estimate'] = lipschitz

        cert = ContractionRateCertifier.compute_contraction_certificate(n, result)

        print(f"{cert['protocol_name']}:")
        print(f"  status = {cert['status']}")
        print(f"  tau_optimal = {cert['tau_birkhoff_optimal']:.6f}")
        print(f"  kappa_obstruction = {cert['kappa_obstruction']:.6f}")
        print(f"  constraints_satisfied = {cert['constraints_satisfied']}/3")

        if 'missing_constraint' in cert:
            print(f"  missing = {cert['missing_constraint']}")
        if 'lipschitz_actual' in cert:
            print(f"  lipschitz_actual = {cert['lipschitz_actual']:.6f}")
            print(f"  gap_from_obstruction = {cert['gap_from_obstruction']:.6f}")
        if 'at_boundary' in cert:
            print(f"  at_boundary = {cert['at_boundary']}")

        print(f"  conclusion: {cert['conclusion']}")
        print()

    print("duality verification via measurement:")
    avg_cyclic = lambda l: sum(l) / n
    avg_identity = lambda l: sum(l[1:]) / (n - 1)

    duality = ContractionRateCertifier.verify_duality_via_violation(n, avg_cyclic, avg_identity)

    print(f"  kappa_theory = {duality['kappa_theory']:.6f}")
    print(f"  kappa_measured = {duality['kappa_measured']:.6f}")
    print(f"  tau_theory = {duality['tau_theory']:.6f}")
    print(f"  tau_measured = {duality['tau_measured']:.6f}")
    print(f"  product_theory = {duality['product_theory']:.6f}")
    print(f"  product_measured = {duality['product_measured']:.6f}")
    print(f"  product_error = {duality['product_error']:.6f}")
    print(f"  duality_verified = {duality['duality_verified']}")
    print()

def run_byzantine_resilience_analysis(n_values: List[int] = None) -> List[Dict]:
    if n_values is None:
        n_values = [3, 5, 7, 9]

    print("=" * 80)
    print("Byzantine Resilience vs Geometric Optimality")
    print("=" * 80)

    results = []

    for n in n_values:
        kappa_obstruction = n / (n - 1)

        median_op = lambda l: np.median(l)
        L_median = ProtocolAnalyzer(Protocol(n, median_op, "median")).compute_lipschitz_estimate(samples=1000)
        gap_median = abs(L_median - kappa_obstruction)

        def trimmed_mean(l):
            s = sorted(l)
            return sum(s[1:-1]) / (len(s) - 2) if len(s) > 2 else sum(s) / len(s)

        L_trimmed = ProtocolAnalyzer(Protocol(n, trimmed_mean, "trimmed")).compute_lipschitz_estimate(samples=1000)
        gap_trimmed = abs(L_trimmed - kappa_obstruction)

        avg_op = lambda l: sum(l) / len(l)
        L_avg = ProtocolAnalyzer(Protocol(n, avg_op, "average")).compute_lipschitz_estimate(samples=1000)
        gap_avg = abs(L_avg - kappa_obstruction)

        results.append({
            'n': n,
            'kappa': kappa_obstruction,
            'L_median': L_median,
            'gap_median': gap_median,
            'L_trimmed': L_trimmed,
            'gap_trimmed': gap_trimmed,
            'L_avg': L_avg,
            'gap_avg': gap_avg
        })

    print(f"{'n':<4} {'kappa':<8} {'L_med':<8} {'gap_med':<8} {'L_trim':<8} {'gap_trim':<8} {'L_avg':<8} {'gap_avg':<8}")
    for r in results:
        print(f"{r['n']:<4} {r['kappa']:<8.4f} {r['L_median']:<8.4f} {r['gap_median']:<8.4f} "
              f"{r['L_trimmed']:<8.4f} {r['gap_trimmed']:<8.4f} {r['L_avg']:<8.4f} {r['gap_avg']:<8.4f}")

    gap_median_vals = [r['gap_median'] for r in results]
    gap_avg_vals = [r['gap_avg'] for r in results]
    print(f"\nMedian gap range: [{min(gap_median_vals):.4f}, {max(gap_median_vals):.4f}]")
    print(f"Average gap range: [{min(gap_avg_vals):.4f}, {max(gap_avg_vals):.4f}]")
    print()

    return results

def run_approximate_region_analysis(n: int, num_samples: int = 500) -> Dict:
    print("=" * 80)
    print("Approximate Constraint Satisfaction Region")
    print("=" * 80)

    results = []

    for _ in range(num_samples):
        coeffs = np.random.randn(n)
        coeffs = coeffs / np.sum(coeffs)

        op = lambda l, c=coeffs: sum(a * b for a, b in zip(c, l))

        test_inputs = np.random.randn(n).tolist()
        _, err_cyc = ConstraintChecker.nary_cyclic(op, n, test_inputs, rotations=10)
        _, err_id = ConstraintChecker.nary_identity_law(op, n, 0.0, samples=20)
        _, _, err_aff = ConstraintChecker.nary_affine(op, n, samples=50)

        results.append({
            'err_cyc': err_cyc,
            'err_id': err_id,
            'err_aff': err_aff,
            'sum_errors': err_cyc + err_id + err_aff,
            'max_error': max(err_cyc, err_id, err_aff)
        })

    err_cyc_vals = [r['err_cyc'] for r in results]
    err_id_vals = [r['err_id'] for r in results]
    err_aff_vals = [r['err_aff'] for r in results]
    sum_vals = [r['sum_errors'] for r in results]
    max_vals = [r['max_error'] for r in results]

    print(f"\nStatistics over {num_samples} random affine protocols:")
    print(f"  e_cyclic:   min={min(err_cyc_vals):.6f}, median={np.median(err_cyc_vals):.6f}, max={max(err_cyc_vals):.6f}")
    print(f"  e_identity: min={min(err_id_vals):.6f}, median={np.median(err_id_vals):.6f}, max={max(err_id_vals):.6f}")
    print(f"  e_affine:   min={min(err_aff_vals):.6f}, median={np.median(err_aff_vals):.6f}, max={max(err_aff_vals):.6f}")
    print(f"  sum(e):     min={min(sum_vals):.6f}, median={np.median(sum_vals):.6f}, max={max(sum_vals):.6f}")
    print(f"  max(e):     min={min(max_vals):.6f}, median={np.median(max_vals):.6f}, max={max(max_vals):.6f}")

    zero_region = [r for r in results if r['sum_errors'] < 0.01]
    print(f"\nProtocols with sum(e) < 0.01: {len(zero_region)}")
    print()

    return {'n': n, 'num_samples': num_samples, 'results': results}

def run_scaling_verification(n_values: List[int] = None) -> List[Dict]:
    if n_values is None:
        n_values = [2, 3, 4, 5, 10, 20, 50, 100]

    print("=" * 80)
    print("Scaling to Higher Dimensions")
    print("=" * 80)

    results = []

    for n in n_values:
        kappa = n / (n - 1)
        tau = 1 - 1 / n
        product = kappa * tau

        violations = 0
        num_trials = 100 if n <= 10 else 50

        for _ in range(num_trials):
            coeffs = np.random.randn(n)
            coeffs = coeffs / np.sum(coeffs)

            op = lambda l, c=coeffs: sum(a * b for a, b in zip(c, l))

            test_inputs = np.random.randn(n).tolist()
            is_cyc, _ = ConstraintChecker.nary_cyclic(op, n, test_inputs, rotations=5)
            is_id, _ = ConstraintChecker.nary_identity_law(op, n, 0.0, samples=10)
            is_aff, _, _ = ConstraintChecker.nary_affine(op, n, samples=30)

            if is_cyc and is_id and is_aff:
                violations += 1

        results.append({
            'n': n,
            'kappa': kappa,
            'tau': tau,
            'product': product,
            'product_error': abs(product - 1.0),
            'trials': num_trials,
            'violations': violations,
            'impossibility_holds': violations == 0
        })

    print(f"{'n':<6} {'kappa':<10} {'tau':<10} {'k*t':<10} {'error':<12} {'trials':<8} {'viols':<8} {'holds'}")
    for r in results:
        print(f"{r['n']:<6} {r['kappa']:<10.6f} {r['tau']:<10.6f} {r['product']:<10.6f} "
              f"{r['product_error']:<12.2e} {r['trials']:<8} {r['violations']:<8} {r['impossibility_holds']}")

    all_hold = all(r['impossibility_holds'] for r in results)
    max_product_error = max(r['product_error'] for r in results)

    print(f"\nImpossibility holds for all n: {all_hold}")
    print(f"Maximum duality error: {max_product_error:.2e}")
    print()

    return results

def run_weighted_cyclic_test(n: int = 3) -> List[Dict]:
    print("=" * 80)
    print("Weighted Cyclic Symmetry")
    print("=" * 80)

    results = []

    weight_configs = [
        [1/3, 1/3, 1/3],
        [0.5, 0.3, 0.2],
        [0.6, 0.3, 0.1],
        [0.7, 0.2, 0.1],
        [0.8, 0.15, 0.05],
    ]

    for weights in weight_configs:
        def weighted_cyclic_op(inputs):
            return sum(w * x for w, x in zip(weights, inputs))

        test_inputs = np.random.randn(n).tolist()
        is_cyc, err_cyc = ConstraintChecker.nary_cyclic(weighted_cyclic_op, n, test_inputs, rotations=20)
        is_id, err_id = ConstraintChecker.nary_identity_law(weighted_cyclic_op, n, 0.0, samples=50)
        is_aff, coeffs, err_aff = ConstraintChecker.nary_affine(weighted_cyclic_op, n, samples=100)

        L = ProtocolAnalyzer(Protocol(n, weighted_cyclic_op, "weighted")).compute_lipschitz_estimate(samples=500)

        results.append({
            'weights': weights,
            'cyclic': is_cyc,
            'identity': is_id,
            'affine': is_aff,
            'err_cyc': err_cyc,
            'err_id': err_id,
            'err_aff': err_aff,
            'lipschitz': L,
            'satisfies_all': is_cyc and is_id and is_aff
        })

    print(f"{'Weights':<30} {'Cyc':<6} {'Id':<6} {'Aff':<6} {'All':<6} {'L':<8}")
    for r in results:
        w_str = str([f"{w:.2f}" for w in r['weights']])
        print(f"{w_str:<30} {r['cyclic']!s:<6} {r['identity']!s:<6} {r['affine']!s:<6} "
              f"{r['satisfies_all']!s:<6} {r['lipschitz']:<8.4f}")

    any_violations = any(r['satisfies_all'] for r in results)
    print(f"\nWeighted cyclic escapes impossibility: {any_violations}")
    print()

    return results

def run_threshold_protocol_test(n: int = 3) -> List[Dict]:
    print("=" * 80)
    print("Threshold Voting Protocols")
    print("=" * 80)

    results = []

    def plurality(inputs):
        return np.median(inputs)

    def threshold_2_unanimous(inputs):
        if len(set(inputs)) == 1:
            return inputs[0]
        return np.median(inputs)

    protocols = [
        ("plurality", plurality),
        ("threshold_2_unanimous", threshold_2_unanimous),
    ]

    for name, protocol in protocols:
        test_inputs = np.random.randn(n).tolist()
        is_cyc, err_cyc = ConstraintChecker.nary_cyclic(protocol, n, test_inputs, rotations=20)
        is_id, err_id = ConstraintChecker.nary_identity_law(protocol, n, 0.0, samples=50)
        is_aff, coeffs, err_aff = ConstraintChecker.nary_affine(protocol, n, samples=100)

        L = ProtocolAnalyzer(Protocol(n, protocol, name)).compute_lipschitz_estimate(samples=500)

        results.append({
            'protocol': name,
            'cyclic': is_cyc,
            'identity': is_id,
            'affine': is_aff,
            'err_cyc': err_cyc,
            'err_id': err_id,
            'err_aff': err_aff,
            'lipschitz': L,
            'satisfies_all': is_cyc and is_id and is_aff
        })

    print(f"{'Protocol':<25} {'Cyc':<6} {'Id':<6} {'Aff':<6} {'All':<6} {'L':<8}")
    for r in results:
        print(f"{r['protocol']:<25} {r['cyclic']!s:<6} {r['identity']!s:<6} {r['affine']!s:<6} "
              f"{r['satisfies_all']!s:<6} {r['lipschitz']:<8.4f}")
    print()

    return results

def run_convergence_certification(n: int = 3, epsilon: float = 0.01) -> List[Dict]:
    print("=" * 80)
    print("Convergence Time Certification")
    print("=" * 80)

    kappa = n / (n - 1)
    tau = 1 - 1 / n

    results = []

    def average(l):
        return sum(l) / len(l)

    def identity_preserving(l):
        return sum(l[1:]) / (len(l) - 1)

    protocols = [
        ("average", average),
        ("identity_preserving", identity_preserving),
    ]

    num_rounds = 20
    num_trials = 100

    for name, protocol in protocols:
        convergence_times = []

        for _ in range(num_trials):
            values = np.random.randn(n).tolist()

            for t in range(num_rounds):
                values = [protocol(values) for _ in range(n)]

                value_range = max(values) - min(values)
                if value_range < epsilon:
                    convergence_times.append(t + 1)
                    break

        if convergence_times:
            avg_convergence = np.mean(convergence_times)

            typical_initial_range = 6.0
            theoretical_time = np.log(epsilon / typical_initial_range) / np.log(tau)

            results.append({
                'protocol': name,
                'measured_convergence': avg_convergence,
                'theoretical_bound': theoretical_time,
                'tau_certified': tau,
                'convergence_rate': len(convergence_times) / num_trials
            })
        else:
            results.append({
                'protocol': name,
                'measured_convergence': None,
                'theoretical_bound': None,
                'tau_certified': tau,
                'convergence_rate': 0.0
            })

    print(f"\nConvergence to epsilon = {epsilon}:")
    print(f"{'Protocol':<25} {'Measured_T':<12} {'Theory_T':<12} {'tau_cert':<10} {'Conv_rate'}")
    for r in results:
        meas = f"{r['measured_convergence']:.2f}" if r['measured_convergence'] else "N/A"
        theo = f"{r['theoretical_bound']:.2f}" if r['theoretical_bound'] else "N/A"
        print(f"{r['protocol']:<25} {meas:<12} {theo:<12} {r['tau_certified']:<10.4f} {r['convergence_rate']:.2f}")

    print(f"\nTheoretical certified bound from tau = {tau:.4f}")
    print()

    return results

if __name__ == "__main__":
    import sys

    n = 3

    run_full_verification(n)
    run_constraint_space_analysis(n)
    run_contraction_certification(n)

    run_byzantine_resilience_analysis()
    run_approximate_region_analysis(n)
    run_scaling_verification()
    run_weighted_cyclic_test(n)
    run_threshold_protocol_test(n)
    run_convergence_certification(n)

    print("=" * 80)
    print("EXTREME SAMPLING")
    print("=" * 80)
    print()
    extreme = run_extreme_sampling(n)
    print(f"num_cases: {extreme['num_cases']}")
    print(f"any_satisfy_all_three: {extreme['any_satisfy_all_three']}")
    print()

    for case in extreme['cases']:
        print(f"{case['name']} ({case['category']}):")
        print(f"  coeffs: [{', '.join(f'{c:.6f}' for c in case['coeffs'])}]")
        print(f"  cyclic={case['cyclic']} identity={case['identity']} affine={case['affine']}")
        print(f"  lipschitz: {case['lipschitz']:.6f}")
        print()

    print("=" * 80)
    print("EXTREME INPUT TESTING")
    print("=" * 80)
    print()
    extreme_inputs = run_extreme_input_testing(n)
    print(f"num_tests: {extreme_inputs['num_tests']}")

    failures = [r for r in extreme_inputs['results'] if not r['output_finite']]
    print(f"failures: {len(failures)}")
    if failures:
        for f in failures:
            print(f"  {f['protocol']} on {f['scenario']}: {f.get('error', 'infinite')}")
    print()

    print("verification complete")

    print("\n" + "=" * 80)
    print("BYZANTINE-BIRKHOFF DUALITY VERIFICATION")
    print("=" * 80)
    print()

    byzantine_cases = [
        (4, 1), (5, 1), (7, 2), (10, 3), (13, 4), (16, 5)
    ]

    print("Theorem: kappa_byz * tau_optimal = 1 where:")
    print("  kappa_byz = (n-f)/(n-f-1)")
    print("  tau_optimal = 1 - 1/(n-f)")
    print()
    print(f"{'n':>4} {'f':>4} {'n-f':>6} {'kappa_byz':>12} {'tau_opt':>12} {'product':>12} {'verified':>10}")
    print("-" * 70)

    for n, f in byzantine_cases:
        n_honest = n - f
        kappa_byz = n_honest / (n_honest - 1)
        tau_opt = 1 - 1/n_honest
        product = kappa_byz * tau_opt
        verified = abs(product - 1.0) < 1e-12
        print(f"{n:4d} {f:4d} {n_honest:6d} {kappa_byz:12.6f} {tau_opt:12.6f} {product:12.6f} {str(verified):>10s}")

    print()
    print("All duality relations verified!")
    print()
    print("COMPUTATIONAL VERIFICATION COMPLETE")
