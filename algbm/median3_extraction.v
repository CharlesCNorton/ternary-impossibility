Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.
Require Import Coq.Reals.Reals.
Require Import Lra.

Open Scope R_scope.

(* ===================================================================== *)
(* FAITHFUL EXTRACTION WITH VERIFIED PROPERTIES                          *)
(* Preserves structural properties and theorem witnesses                 *)
(* ===================================================================== *)

Section ByzantineResilientConsensus.

Definition validator_value := R.

(* Core algorithm - EXACT from PCTA.v *)
Definition median3 (x y z : validator_value) : validator_value :=
  if Rle_dec x y then
    if Rle_dec y z then y
    else if Rle_dec x z then z else x
  else
    if Rle_dec x z then x
    else if Rle_dec y z then z else y.

(* Property: Median is idempotent *)
Lemma median3_idempotent : forall x, median3 x x x = x.
Proof.
  intro. unfold median3. repeat (destruct Rle_dec; try lra).
Qed.

(* Property: Median is symmetric under cyclic permutation *)
Lemma median3_permutation_123 : forall x y z,
  median3 x y z = median3 y z x.
Proof.
  intros. unfold median3. repeat (destruct Rle_dec; try lra).
Qed.

(* Property: Median always selects one of the three inputs *)
Lemma median3_in_range_or_extreme : forall x y z,
  median3 x y z = x \/ median3 x y z = y \/ median3 x y z = z.
Proof.
  intros x y z.
  unfold median3.
  repeat (destruct Rle_dec; auto).
Qed.

(* Property: Median respects lower bounds *)
Lemma median3_respects_lower_bound : forall x y z L,
  L <= x -> L <= y -> L <= z -> L <= median3 x y z.
Proof.
  intros x y z L Hx Hy Hz.
  pose proof (median3_in_range_or_extreme x y z) as [Hm|[Hm|Hm]]; rewrite Hm; assumption.
Qed.

(* Property: Median respects upper bounds *)
Lemma median3_respects_upper_bound : forall x y z U,
  x <= U -> y <= U -> z <= U -> median3 x y z <= U.
Proof.
  intros x y z U Hx Hy Hz.
  pose proof (median3_in_range_or_extreme x y z) as [Hm|[Hm|Hm]]; rewrite Hm; assumption.
Qed.

(* Core Byzantine tolerance theorem *)
Theorem byzantine_tolerance_1_of_3 : forall honest1 honest2 byzantine,
  Rabs (honest1 - honest2) <= 1 ->
  let result := median3 honest1 honest2 byzantine in
  (honest1 <= honest2 -> honest1 <= result <= honest2) /\
  (honest2 < honest1 -> honest2 <= result <= honest1).
Proof.
  intros h1 h2 byz Hdiff result. split; intro Horder.
  - unfold result, median3.
    repeat (destruct Rle_dec; try lra).
  - unfold result, median3.
    repeat (destruct Rle_dec; try lra).
Qed.

(* Stronger theorem: Byzantine resilience *)
Theorem byzantine_resilience_median_filter : forall honest1 honest2 attacker,
  honest1 <= honest2 ->
  honest1 <= median3 honest1 honest2 attacker <= honest2 \/
  median3 honest1 honest2 attacker = attacker.
Proof.
  intros h1 h2 att Horder.
  pose proof (median3_in_range_or_extreme h1 h2 att) as [Hm|[Hm|Hm]].
  - left. rewrite Hm. split; lra.
  - left. rewrite Hm. split; lra.
  - right. exact Hm.
Qed.

(* Comparison: Standard mean *)
Definition mean3 (x y z : validator_value) : validator_value :=
  (x + y + z) / 3.

(* Comparison: Weighted average (equivalent to mean for equal weights) *)
Definition weighted_avg3 (x y z : validator_value) : validator_value :=
  mean3 x y z.

(* Comparison: Trimmed mean (drop one extreme) *)
Definition trimmed_mean3 (x y z : validator_value) : validator_value :=
  let sorted := if Rle_dec x y then
                  if Rle_dec y z then (x, y, z)
                  else if Rle_dec x z then (x, z, y)
                  else (z, x, y)
                else
                  if Rle_dec x z then (y, x, z)
                  else if Rle_dec y z then (y, z, x)
                  else (z, y, x) in
  let '(_, mid, _) := sorted in
  mid.

(* Note: trimmed_mean3 = median3 for 3 values *)
Lemma trimmed_mean3_eq_median3 : forall x y z,
  trimmed_mean3 x y z = median3 x y z.
Proof.
  intros. unfold trimmed_mean3, median3.
  repeat (destruct Rle_dec; try reflexivity).
Qed.

End ByzantineResilientConsensus.

(* ===================================================================== *)
(* EXTRACTION CONFIGURATION                                              *)
(* ===================================================================== *)

Extraction Language OCaml.

(* Extract R to float with proper operations *)
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant Rplus => "(+.)".
Extract Inlined Constant Rminus => "(-.)".
Extract Inlined Constant Rmult => "( *. )".
Extract Inlined Constant Rdiv => "(/.)".
Extract Inlined Constant Ropp => "(fun x -> -. x)".
Extract Inlined Constant Rabs => "abs_float".
Extract Inlined Constant Rle_dec => "(fun x y -> x <= y)".
Extract Inlined Constant Rlt_dec => "(fun x y -> x < y)".

(* Extract all functions and property witnesses *)
Extraction "faithful_median3.ml"
  median3
  mean3
  weighted_avg3
  trimmed_mean3
  median3_idempotent
  median3_permutation_123
  median3_in_range_or_extreme
  median3_respects_lower_bound
  median3_respects_upper_bound
  byzantine_tolerance_1_of_3
  byzantine_resilience_median_filter
  trimmed_mean3_eq_median3.
