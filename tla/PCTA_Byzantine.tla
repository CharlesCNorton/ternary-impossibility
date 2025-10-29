---------------------- MODULE PCTA_Byzantine ----------------------
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS N, F, MAX_ROUNDS, INITIAL_VAL, ATTACK_MAG

ASSUME N \in Nat /\ N >= 3
ASSUME F \in Nat /\ F >= 0 /\ F < N
ASSUME MAX_ROUNDS \in Nat /\ MAX_ROUNDS > 0

Nodes == 1..N
HonestNodes == 1..(N-F)
ByzantineNodes == (N-F+1)..N

VARIABLES
  round,
  honest_val,      \* Single value for all honest nodes (they converge)
  byz_val,         \* Current Byzantine attack value
  median_history,
  avg_history,
  median_violated,
  avg_violated,
  ternary_history  \* Track ternary operation with d=2

vars == <<round, honest_val, byz_val, median_history, avg_history, median_violated, avg_violated, ternary_history>>

-----------------------------------------------------------------------------

\* Simple median for 3 values (2 honest + 1 Byzantine)
Median3(a, b, c) ==
  IF a <= b /\ b <= c THEN b
  ELSE IF a <= c /\ c <= b THEN c
  ELSE IF b <= a /\ a <= c THEN a
  ELSE IF b <= c /\ c <= a THEN c
  ELSE IF c <= a /\ a <= b THEN a
  ELSE b

\* Median for N honest nodes with same value + F Byzantine with same value
\* When honest nodes converge, median is determined by majority
MedianNValues(honest, byzantine, n_honest, n_byz) ==
  IF n_honest > n_byz THEN honest
  ELSE IF n_byz > n_honest THEN byzantine
  ELSE (honest + byzantine) \div 2  \* Tie-breaking

\* Average of values
AverageNValues(honest, byzantine, n_honest, n_byz) ==
  (honest * n_honest + byzantine * n_byz) \div (n_honest + n_byz)

\* In bounds check
InBounds(v, lower, upper) == v >= lower /\ v <= upper

-----------------------------------------------------------------------------

Init ==
  /\ round = 0
  /\ honest_val = INITIAL_VAL
  /\ byz_val = ATTACK_MAG
  /\ median_history = <<INITIAL_VAL>>
  /\ avg_history = <<INITIAL_VAL>>
  /\ ternary_history = <<INITIAL_VAL>>
  /\ median_violated = FALSE
  /\ avg_violated = FALSE

-----------------------------------------------------------------------------

\* Byzantine alternating attack
ByzantineAttack ==
  IF round % 2 = 0 THEN ATTACK_MAG ELSE -ATTACK_MAG

\* Ternary operation with d=2 (for Lipschitz verification)
TernaryD2(x) == (3 * x) \div 2

\* Median aggregation step
MedianStep ==
  /\ round < MAX_ROUNDS
  /\ LET attack == ByzantineAttack
         n_honest == N - F
         n_byz == F
         result == MedianNValues(honest_val, attack, n_honest, n_byz)
         violated == ~InBounds(result, INITIAL_VAL - 10, INITIAL_VAL + 10)
     IN /\ honest_val' = result
        /\ byz_val' = attack
        /\ median_history' = Append(median_history, result)
        /\ median_violated' = (median_violated \/ violated)
        /\ round' = round + 1
        /\ avg_history' = avg_history
        /\ avg_violated' = avg_violated
        /\ ternary_history' = ternary_history

\* Average aggregation step
AverageStep ==
  /\ round < MAX_ROUNDS
  /\ LET attack == ByzantineAttack
         n_honest == N - F
         n_byz == F
         result == AverageNValues(honest_val, attack, n_honest, n_byz)
         violated == ~InBounds(result, INITIAL_VAL - 20, INITIAL_VAL + 20)
     IN /\ honest_val' = result
        /\ byz_val' = attack
        /\ avg_history' = Append(avg_history, result)
        /\ avg_violated' = (avg_violated \/ violated)
        /\ round' = round + 1
        /\ median_history' = median_history
        /\ median_violated' = median_violated
        /\ ternary_history' = ternary_history

\* Ternary operation step (d=2, demonstrates Lipschitz 3/2 growth)
TernaryStep ==
  /\ round < MAX_ROUNDS
  /\ LET result == TernaryD2(honest_val)
     IN /\ honest_val' = result
        /\ byz_val' = 0
        /\ ternary_history' = Append(ternary_history, result)
        /\ round' = round + 1
        /\ median_history' = median_history
        /\ avg_history' = avg_history
        /\ median_violated' = median_violated
        /\ avg_violated' = avg_violated

-----------------------------------------------------------------------------

Next == MedianStep \/ AverageStep \/ TernaryStep

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
  /\ round \in 0..MAX_ROUNDS
  /\ honest_val \in Int
  /\ byz_val \in Int
  /\ median_history \in Seq(Int)
  /\ avg_history \in Seq(Int)
  /\ ternary_history \in Seq(Int)

\* Main safety property: median stays in bounds when f < n/3
MedianSafe ==
  (3 * F < N) => ~median_violated

\* Average should eventually violate when f >= n/3
AverageUnsafe ==
  (3 * F >= N) => <>(avg_violated)

\* Bounds should hold for median path
MedianBounded ==
  (3 * F < N) =>
    \A i \in DOMAIN median_history:
      InBounds(median_history[i], INITIAL_VAL - 10, INITIAL_VAL + 10)

\* Average should NOT violate (we expect this to fail with f >= n/3)
AverageNeverViolates == ~avg_violated

\* Ternary growth matches Lipschitz bound (approximate check)
\* After n iterations: value should be approximately INITIAL_VAL * (3/2)^n
\* For n=12: (3/2)^12 ≈ 129.7, so 100 * 129.7 ≈ 12970
TernaryGrowthBound ==
  round <= 12 =>
    ternary_history[round + 1] <= INITIAL_VAL * 200

StateConstraint ==
  /\ round <= MAX_ROUNDS
  /\ honest_val >= -10000
  /\ honest_val <= 100000

=============================================================================
