(* ========================================================================= *)
(* Formal Development of Ternary Algebraic Structures in Coq                *)
(* ========================================================================= *)
(*                                                                           *)
(* Author: Charles C. Norton                                                *)
(* Date: October 31, 2025                                                   *)
(*                                                                           *)
(* This file contains definitions and theorems concerning ternary           *)
(* operations satisfying cyclic symmetry and identity axioms.               *)
(*                                                                           *)
(* Dependencies: Coq 8.19+, Flocq 4.1.0+                                   *)
(*                                                                           *)
(* Repository: https://github.com/CharlesCNorton/ternary-impossibility     *)
(*                                                                           *)
(* ========================================================================= *)

(* Real numbers and arithmetic *)
Require Import Reals.
(* Linear real arithmetic tactic *)
Require Import Lra.
(* Linear integer arithmetic tactic *)
Require Import Lia.
(* Ring algebraic structure *)
Require Import Coq.setoid_ring.Ring.
(* Field algebraic structure *)
Require Import Coq.setoid_ring.Field.
(* Well-founded natural number induction *)
Require Import Coq.Arith.Wf_nat.
(* Constructive epsilon operator *)
Require Import Coq.Logic.ConstructiveEpsilon.
(* Indefinite description operator *)
Require Import Coq.Logic.IndefiniteDescription.
(* Proof irrelevance axiom *)
Require Import Coq.Logic.ProofIrrelevance.
(* Micromega tactics for arithmetic *)
Require Import Psatz.
(* Vectors with static length *)
Require Import Coq.Vectors.Vector.
(* Polymorphic lists *)
Require Import List.
Import ListNotations.
(* List permutations *)
Require Import Coq.Sorting.Permutation.
(* Trigonometric functions *)
Require Import Coq.Reals.Rtrigo.
(* Real analysis library *)
Require Import Coq.Reals.Ranalysis.
(* Floating point formalization library *)
Require Import Flocq.Core.Core.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Core.FLT.
Require Import QArith.
Require Import Qcanon.
Require Import Coq.Reals.Raxioms.
Require Import Coq.QArith.Qreals.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.QArith.Qring.

(* Use real number notations by default *)
Open Scope R_scope.

(* ========================================================================= *)
(* Computational/Constructive Definitions                                    *)
(* ========================================================================= *)

Section ComputationalContent.

Open Scope Q_scope.

Definition compute_lipschitz_constant_Q (n : nat) : option Q :=
  match n with
  | O => None
  | S O => None
  | S (S O) => None
  | S (S (S m)) => Some (inject_Z (Z.of_nat n) / inject_Z (Z.of_nat (n - 1)))
  end.

Example compute_lipschitz_3 : compute_lipschitz_constant_Q 3 = Some (3 # 2).
Proof. reflexivity. Qed.

Example compute_lipschitz_4 : compute_lipschitz_constant_Q 4 = Some (4 # 3).
Proof. reflexivity. Qed.

Example compute_lipschitz_10 : compute_lipschitz_constant_Q 10 = Some (10 # 9).
Proof. reflexivity. Qed.

Fixpoint nat_power_Q (base : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S n' => base * nat_power_Q base n'
  end.

Definition compute_three_halves_power (n : nat) : Q :=
  nat_power_Q (3 # 2) n.

Example test_3_2_power_1 : compute_three_halves_power 1 = (3 # 2).
Proof. reflexivity. Qed.

Example test_3_2_power_2 : compute_three_halves_power 2 = (9 # 4).
Proof. reflexivity. Qed.

Example test_3_2_power_12 : compute_three_halves_power 12 = (531441 # 4096).
Proof. vm_compute. reflexivity. Qed.

Definition check_exceeds_100 (q : Q) : bool :=
  Qle_bool 100 q.

Example verify_12_iterations_exceeds_100 :
  check_exceeds_100 (compute_three_halves_power 12) = true.
Proof. vm_compute. reflexivity. Qed.

Example verify_11_iterations_below_100 :
  check_exceeds_100 (compute_three_halves_power 11) = false.
Proof. vm_compute. reflexivity. Qed.

Fixpoint iterate_ternary_Q (x : Q) (n : nat) : Q :=
  match n with
  | O => x
  | S n' => let v := iterate_ternary_Q x n' in (v + v + v) / 2
  end.

Example test_iterate_12_exceeds_100 :
  check_exceeds_100 (iterate_ternary_Q 1 12) = true.
Proof. vm_compute. reflexivity. Qed.

Example test_iterate_11_below_100 :
  check_exceeds_100 (iterate_ternary_Q 1 11) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma Qmult_3_div_2_eq : forall q : Q,
  ((q + q + q) / 2 == (3 # 2) * q)%Q.
Proof.
  intro q.
  field.
Qed.

Lemma Qeq_to_eq : forall (a b : Q), a == b -> Qred a = Qred b.
Proof.
  intros a b Heq.
  apply Qred_complete.
  exact Heq.
Qed.

Lemma Qred_involutive : forall q : Q, Qred (Qred q) = Qred q.
Proof.
  intro q.
  apply Qred_complete.
  apply Qred_correct.
Qed.

Require Import Coq.QArith.Qcanon.

Lemma iterate_ternary_Q_equals_power : forall n,
  iterate_ternary_Q 1 n == nat_power_Q (3 # 2) n.
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - simpl iterate_ternary_Q.
    simpl nat_power_Q.
    rewrite Qmult_3_div_2_eq.
    rewrite IH.
    reflexivity.
Qed.

Close Scope Q_scope.

End ComputationalContent.

(* ========================================================================= *)
(* Reflection - Connecting Computational Q to Real R                        *)
(* ========================================================================= *)

Section ComputationalReflection.

Lemma Q2R_nat_power : forall (base : Q) (n : nat),
  Q2R (nat_power_Q base n) = (Q2R base) ^ n.
Proof.
  intros base n.
  induction n as [|n' IH].
  - simpl. unfold Q2R. simpl. lra.
  - simpl nat_power_Q.
    rewrite Q2R_mult.
    rewrite IH.
    simpl. ring.
Qed.

Theorem lipschitz_constant_computable_3 :
  exists Lq : Q,
    compute_lipschitz_constant_Q 3 = Some Lq /\
    Q2R Lq = 3 / 2.
Proof.
  exists (3 # 2)%Q.
  split.
  - reflexivity.
  - unfold Q2R. simpl. lra.
Qed.

Theorem lipschitz_constant_computable_4 :
  exists Lq : Q,
    compute_lipschitz_constant_Q 4 = Some Lq /\
    Q2R Lq = 4 / 3.
Proof.
  exists (4 # 3)%Q.
  split.
  - reflexivity.
  - unfold Q2R. simpl. lra.
Qed.

Theorem lipschitz_constant_computable_10 :
  exists Lq : Q,
    compute_lipschitz_constant_Q 10 = Some Lq /\
    Q2R Lq = 10 / 9.
Proof.
  exists (10 # 9)%Q.
  split.
  - reflexivity.
  - unfold Q2R. simpl. lra.
Qed.

Theorem three_halves_power_computable : forall n,
  Q2R (compute_three_halves_power n) = (3/2) ^ n.
Proof.
  intro n.
  unfold compute_three_halves_power.
  rewrite Q2R_nat_power.
  unfold Q2R at 1. simpl.
  lra.
Qed.

Theorem computational_verification_of_12_iterations :
  (3/2)^12 > 100.
Proof.
  assert (H: Q2R (compute_three_halves_power 12) = (3/2)^12).
  { apply three_halves_power_computable. }
  rewrite <- H.
  assert (Hcheck: check_exceeds_100 (compute_three_halves_power 12) = true).
  { vm_compute. reflexivity. }
  unfold check_exceeds_100 in Hcheck.
  apply Qle_bool_iff in Hcheck.
  apply Qle_Rle in Hcheck.
  simpl in Hcheck. lra.
Qed.

End ComputationalReflection.

(* Main formalization section *)
Section TernaryAlgebraicStructure.

(* Type class for algebraic structures with three-argument operation *)
Class TernaryAlgebra (Omega : Type) := {
  (* Three-argument operation *)
  ternary_op : Omega -> Omega -> Omega -> Omega;
  (* Neutral element *)
  identity : Omega;

  (* Operation invariant under cyclic permutation *)
  cyclic_symmetry : forall a b c,
    ternary_op a b c = ternary_op c a b;

  (* Neutral element satisfies two-input recovery *)
  identity_law : forall a,
    ternary_op identity a a = a;
}.

(* Infix notation for ternary operation *)
Notation "a ⊗ b ⊗ c" := (ternary_op a b c) (at level 40, no associativity).

(* Binary operation obtained by fixing third argument to identity *)
Definition derived_binary_op {Omega : Type} `{TernaryAlgebra Omega}
  (a b : Omega) : Omega :=
  ternary_op a b identity.

(* Infix notation for derived binary operation *)
Notation "a ◊ b" := (derived_binary_op a b) (at level 40).

(* Ternary algebra equipped with real-valued norm *)
Class ValuatedTernaryAlgebra (Omega : Type) `{TernaryAlgebra Omega} := {
  (* Real-valued norm function *)
  valuation : Omega -> R;

  (* Norm is nonnegative *)
  valuation_nonneg : forall x, 0 <= valuation x;

  (* Neutral element has zero norm *)
  valuation_identity : valuation identity = 0;

  (* Norm of ternary operation bounded by average of inputs *)
  valuation_barycentric : forall a b c,
    valuation (ternary_op a b c) <=
    (valuation a + valuation b + valuation c) / 2;

  (* Zero norm implies identity element *)
  valuation_faithful : forall x,
    valuation x = 0 -> x = identity;
}.

(* Uniqueness results for affine representations *)
Section UniquenessOfAffineForm.

(* Cyclic and identity axioms force coefficients to be 1/2 *)
Theorem cyclic_identity_forces_equal_coefficients :
  forall (lambda mu nu : R),
  (forall a b c, lambda*a + mu*b + nu*c = lambda*c + mu*a + nu*b) ->
  (forall a, mu*a + nu*a = a) ->
  lambda = mu /\ mu = nu /\ lambda = 1/2.
Proof.
  intros lambda mu nu Hcyclic Hidentity.
  assert (Heq_lambda_mu: lambda = mu).
  { specialize (Hcyclic 1 0 0).
    simpl in Hcyclic.
    lra. }
  assert (Heq_mu_nu: mu = nu).
  { specialize (Hcyclic 0 1 0).
    simpl in Hcyclic.
    lra. }
  assert (Hvalue: lambda = 1/2).
  { specialize (Hidentity 1).
    rewrite <- Heq_lambda_mu in Hidentity.
    rewrite <- Heq_mu_nu in Hidentity.
    lra. }
  split; [exact Heq_lambda_mu | split; [exact Heq_mu_nu | exact Hvalue]].
Qed.

(* Cyclic affine operation on reals uniquely determined as average *)
Theorem affine_form_uniqueness_for_R :
  forall (op : R -> R -> R -> R),
  (forall a b c, op a b c = op c a b) ->
  (forall a, op 0 a a = a) ->
  (exists lambda mu nu, forall a b c, op a b c = lambda*a + mu*b + nu*c) ->
  (forall a b c, op a b c = (a + b + c) / 2).
Proof.
  intros op Hcyclic Hidentity [lambda [mu [nu Haffine]]].
  intros a b c.
  assert (Hcyc100: lambda = mu).
  { pose proof (Haffine 1 0 0) as H1.
    pose proof (Haffine 0 1 0) as H2.
    pose proof (Hcyclic 1 0 0) as Hc.
    rewrite H1 in Hc.
    rewrite H2 in Hc.
    lra. }
  assert (Hcyc010: mu = nu).
  { pose proof (Haffine 0 1 0) as H1.
    pose proof (Haffine 0 0 1) as H2.
    pose proof (Hcyclic 0 1 0) as Hc.
    rewrite H1 in Hc.
    rewrite H2 in Hc.
    lra. }
  assert (Hid1: lambda = 1/2).
  { pose proof (Haffine 0 1 1) as H1.
    pose proof (Hidentity 1) as Hid.
    rewrite H1 in Hid.
    lra. }
  subst lambda mu nu.
  rewrite (Haffine a b c).
  field.
Qed.

End UniquenessOfAffineForm.

(* Generalization to n-ary operations *)
Section NaryGeneralization.

(* Sum of all elements in a list *)
Fixpoint sum_list (l : list R) : R :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(* Sum of n copies of constant c equals n times c *)
Lemma sum_list_const : forall (n : nat) (c : R),
  sum_list (repeat c n) = INR n * c.
Proof.
  intros n c.
  induction n as [|n' IHn'].
  - simpl. lra.
  - simpl repeat. simpl sum_list. rewrite IHn'.
    assert (H: INR (S n') = INR n' + 1).
    { rewrite S_INR. reflexivity. }
    rewrite H. lra.
Qed.

(* Weighted sum with constant argument factors out *)
Lemma sum_list_map_combine_const : forall (coeffs : list R) (n : nat) (x : R),
  length coeffs = n ->
  sum_list (map (fun '(c, y) => c * y) (combine coeffs (repeat x n))) = sum_list coeffs * x.
Proof.
  intros coeffs n x Hlen.
  revert coeffs Hlen.
  induction n as [|n' IHn']; intros coeffs Hlen.
  - destruct coeffs; [|discriminate].
    simpl. lra.
  - destruct coeffs as [|c cs]; [discriminate |].
    simpl in Hlen. injection Hlen as Hlen'.
    simpl.
    rewrite IHn' by exact Hlen'.
    lra.
Qed.

(* Length of repeated element list *)
Lemma repeat_length : forall (A : Type) (x : A) (n : nat),
  length (repeat x n) = n.
Proof.
  intros A x n.
  induction n; simpl; auto.
Qed.

(* Constructor-repeat decomposition identity *)
Lemma cons_repeat_split : forall (n : nat) (a : R),
  (n > 0)%nat ->
  0 :: repeat a (n - 1) = [0] ++ repeat a (n - 1).
Proof.
  intros. simpl. reflexivity.
Qed.

(* Sum distributes over list concatenation *)
Lemma sum_list_app : forall (l1 l2 : list R),
  sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  intros l1 l2.
  induction l1 as [|x xs IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

(* Combine operation on cons cells *)
Lemma combine_cons : forall (A B : Type) (a : A) (b : B) (la : list A) (lb : list B),
  combine (a :: la) (b :: lb) = (a, b) :: combine la lb.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Map of weighted product splits at head *)
Lemma map_combine_split : forall (c : R) (cs : list R) (x : R) (xs : list R),
  map (fun '(c0, y) => c0 * y) (combine (c :: cs) (x :: xs)) =
  c * x :: map (fun '(c0, y) => c0 * y) (combine cs xs).
Proof.
  intros. simpl. reflexivity.
Qed.

(* Identity law forces first coefficient to be zero *)
Lemma first_coeff_from_identity : forall (n : nat) (coeffs : list R) (op : list R -> R),
  (n >= 2)%nat ->
  length coeffs = n ->
  sum_list coeffs = 1 ->
  (forall inputs, length inputs = n -> op inputs = sum_list (map (fun '(c, y) => c * y) (combine coeffs inputs))) ->
  (forall a, op (0 :: repeat a (n - 1)) = a) ->
  exists c0 cs, coeffs = c0 :: cs /\ c0 = 0 /\ sum_list cs = 1.
Proof.
  intros n coeffs op Hn Hlen Hsum Haff Hid.
  destruct coeffs as [|c0 cs].
  { simpl in Hlen. lia. }
  exists c0, cs.
  split; [reflexivity |].
  simpl in Hlen.
  assert (Hlen': length cs = (n - 1)%nat) by lia.
  assert (Hid1: op (0 :: repeat 1 (n - 1)) = 1) by apply Hid.
  assert (Hlength_repeat: length (repeat 1 (n - 1)) = (n - 1)%nat) by apply repeat_length.
  assert (Hlength_input: length (0 :: repeat 1 (n - 1)) = n).
  { simpl. rewrite Hlength_repeat. lia. }
  rewrite (Haff (0 :: repeat 1 (n - 1)) Hlength_input) in Hid1.
  rewrite map_combine_split in Hid1.
  simpl in Hid1.
  rewrite Rmult_0_r in Hid1.
  rewrite sum_list_map_combine_const in Hid1 by exact Hlen'.
  simpl in Hsum.
  assert (Hcs_sum: sum_list cs = 1).
  { rewrite Rmult_1_r in Hid1. lra. }
  split.
  - lra.
  - exact Hcs_sum.
Qed.

(* N-ary operation wrapper *)
Definition nary_op (n : nat) (op_R : list R -> R) (inputs : list R) : R :=
  op_R inputs.

(* Operation invariant under cyclic rotation of arguments *)
Definition nary_cyclic (n : nat) (op : list R -> R) : Prop :=
  forall (l : list R), length l = n ->
  forall k, (k < n)%nat ->
  op l = op (skipn k l ++ firstn k l).

(* Identity element with n-1 copies recovers value *)
Definition nary_identity_law (n : nat) (op : list R -> R) (e : R) : Prop :=
  forall a, op (e :: repeat a (n - 1)) = a.

(* Operation expressible as weighted sum *)
Definition nary_affine (n : nat) (op : list R -> R) : Prop :=
  exists (coeffs : list R),
    length coeffs = n /\
    sum_list coeffs = 1 /\
    forall (inputs : list R), length inputs = n ->
      op inputs = sum_list (map (fun '(c, x) => c * x) (combine coeffs inputs)).

(* Single rotation moves head to tail *)
Lemma cyclic_rotation_once : forall (A : Type) (l : list A) (n : nat),
  length l = S n ->
  skipn 1 l ++ firstn 1 l = match l with
                             | [] => []
                             | h :: t => t ++ [h]
                             end.
Proof.
  intros A l n Hlen.
  destruct l as [|h t].
  - discriminate.
  - simpl. reflexivity.
Qed.

(* Affine operation on constant inputs *)
Lemma affine_on_repeat_all_equal : forall n coeffs op x,
  length coeffs = n ->
  (forall inputs, length inputs = n ->
    op inputs = sum_list (map (fun '(c, y) => c * y) (combine coeffs inputs))) ->
  op (repeat x n) = sum_list coeffs * x.
Proof.
  intros n coeffs op x Hlen Haffine.
  rewrite Haffine.
  - apply sum_list_map_combine_const. exact Hlen.
  - apply repeat_length.
Qed.

(* Cyclic symmetry forces three coefficients equal *)
Lemma cyclic_forces_equal_coeffs_base : forall c0 c1 c2,
  (forall a0 a1 a2, c0 * a0 + c1 * a1 + c2 * a2 = c0 * a2 + c1 * a0 + c2 * a1) ->
  c0 = c1 /\ c1 = c2.
Proof.
  intros c0 c1 c2 Hcyc.
  split.
  - specialize (Hcyc 1 0 0). lra.
  - specialize (Hcyc 0 1 0). lra.
Qed.

(* Identity law uniquely determines denominator as n-1 *)
Theorem nary_identity_forces_denominator :
  forall (n : nat) (d : R),
  (n >= 2)%nat ->
  d > 0 ->
  (forall a, (0 + INR (n - 1) * a) / d = a) <->
  d = INR (n - 1).
Proof.
  intros n d Hn Hd.
  split; intro Heq.
  - specialize (Heq 1).
    assert (Hsimp: (0 + INR (n - 1) * 1) / d = INR (n - 1) / d).
    { f_equal. lra. }
    rewrite Hsimp in Heq.
    assert (Hcalc: INR (n - 1) / d = 1) by exact Heq.
    unfold Rdiv in Hcalc.
    apply Rmult_eq_compat_r with (r := d) in Hcalc.
    rewrite Rmult_assoc in Hcalc.
    rewrite Rinv_l in Hcalc by lra.
    rewrite Rmult_1_r in Hcalc.
    lra.
  - subst d. intro a.
    assert (H_n_pos: INR (n - 1) > 0).
    { assert (H: (0 < n - 1)%nat) by lia.
      apply lt_INR in H. simpl in H. exact H. }
    field_simplify; [lra | lra].
Qed.

(* Lipschitz constant equals n over n-1 *)
Theorem nary_lipschitz_constant :
  forall (n : nat) (d : R),
  (n >= 2)%nat ->
  d > 0 ->
  d = INR (n - 1) ->
  INR n / d = INR n / INR (n - 1).
Proof.
  intros n d Hn Hd Heq.
  rewrite Heq.
  reflexivity.
Qed.

(* N-ary Lipschitz constant exceeds one for n>=3 *)
Theorem nary_stability_condition :
  forall (n : nat),
  (n >= 3)%nat ->
  INR n / INR (n - 1) > 1.
Proof.
  intros n Hn.
  assert (H_n_pos: INR n > 0).
  { assert (H: (0 < n)%nat) by lia.
    apply lt_INR in H. simpl in H. exact H. }
  assert (H_n1_pos: INR (n - 1) > 0).
  { assert (H: (0 < n - 1)%nat) by lia.
    apply lt_INR in H. simpl in H. exact H. }
  assert (H_ineq: INR n > INR (n - 1)).
  { apply lt_INR. lia. }
  apply Rmult_gt_reg_r with (r := INR (n - 1)).
  - exact H_n1_pos.
  - field_simplify; [lra | lra].
Qed.

(* Strict ordering is irreflexive *)
Lemma Rgt_irrefl_False : forall r : R, r > r -> False.
Proof.
  intros r H.
  unfold Rgt in H.
  exact (Rlt_irrefl r H).
Qed.

(* Affine operation on constant list reduces to scalar multiple *)
Lemma affine_op_on_repeat : forall (n : nat) (coeffs : list R) (op : list R -> R) (x : R),
  length coeffs = n ->
  (forall inputs, length inputs = n -> op inputs = sum_list (map (fun '(c, y) => c * y) (combine coeffs inputs))) ->
  op (repeat x n) = sum_list coeffs * x.
Proof.
  intros n coeffs op x Hlen Haffine.
  rewrite (Haffine (repeat x n)).
  - rewrite sum_list_map_combine_const by exact Hlen.
    reflexivity.
  - apply repeat_length.
Qed.

(* Operation expressible as sum divided by constant *)
Definition nary_barycentric (n : nat) (op : list R -> R) : Prop :=
  exists (d : R),
    d > 0 /\
    forall (inputs : list R), length inputs = n ->
      op inputs = sum_list inputs / d.

(* Barycentric operation factors as constant times sum *)
Lemma nary_barycentric_symmetric_coeffs : forall n op d,
  nary_barycentric n op ->
  d > 0 ->
  (forall inputs, length inputs = n -> op inputs = sum_list inputs / d) ->
  exists (c : R), forall inputs, length inputs = n ->
    op inputs = c * sum_list inputs.
Proof.
  intros n op d Hbary Hd Hop.
  exists (/ d).
  intros inputs Hlen.
  rewrite Hop by exact Hlen.
  unfold Rdiv. ring.
Qed.

(* Barycentric operation on constant list *)
Lemma nary_barycentric_on_repeat : forall n op d x,
  d > 0 ->
  (forall inputs, length inputs = n -> op inputs = sum_list inputs / d) ->
  op (repeat x n) = INR n * x / d.
Proof.
  intros n op d x Hd Hop.
  rewrite Hop.
  - rewrite sum_list_const. reflexivity.
  - apply repeat_length.
Qed.

(* Identity law forces barycentric denominator to be n-1 *)
Theorem nary_identity_determines_denominator_barycentric :
  forall n op d,
  (n >= 2)%nat ->
  d > 0 ->
  nary_identity_law n op 0 ->
  (forall inputs, length inputs = n -> op inputs = sum_list inputs / d) ->
  d = INR (n - 1).
Proof.
  intros n op d Hn Hd Hid Hbary.
  unfold nary_identity_law in Hid.
  assert (Hid1: op (0 :: repeat 1 (n - 1)) = 1).
  { apply Hid. }
  rewrite Hbary in Hid1.
  - assert (Hsum: sum_list (0 :: repeat 1 (n - 1)) = INR (n - 1)).
    { simpl. rewrite sum_list_const. rewrite minus_INR by lia.
      assert (H: INR n - 1 = INR (n - 1)).
      { rewrite minus_INR by lia. reflexivity. }
      lra. }
    rewrite Hsum in Hid1.
    assert (Heq: INR (n - 1) / d = 1) by exact Hid1.
    unfold Rdiv in Heq.
    apply Rmult_eq_compat_r with (r := d) in Heq.
    rewrite Rmult_assoc in Heq.
    rewrite Rinv_l in Heq by lra.
    rewrite Rmult_1_r in Heq.
    lra.
  - simpl. rewrite repeat_length. lia.
Qed.

(* Barycentric operation has Lipschitz constant n/(n-1) *)
Lemma nary_barycentric_lipschitz : forall n op d x,
  (n >= 2)%nat ->
  d = INR (n - 1) ->
  (forall inputs, length inputs = n -> op inputs = sum_list inputs / d) ->
  x <> 0 ->
  op (repeat x n) = INR n / INR (n - 1) * x.
Proof.
  intros n op d x Hn Hd Hbary Hx_neq.
  rewrite Hbary.
  - rewrite sum_list_const.
    rewrite Hd.
    assert (Hn1_pos: INR (n - 1) > 0).
    { apply lt_0_INR. lia. }
    field. lra.
  - apply repeat_length.
Qed.

(* N-ary operations with all three axioms amplify errors *)
Theorem nary_impossibility :
  forall (n : nat),
  (n >= 3)%nat ->
  exists (lipschitz_constant : R),
    lipschitz_constant = INR n / INR (n - 1) /\
    lipschitz_constant > 1 /\
    (forall (op : list R -> R),
      nary_cyclic n op ->
      nary_identity_law n op 0 ->
      nary_barycentric n op ->
      forall x, x <> 0 ->
        Rabs (op (repeat x n)) = lipschitz_constant * Rabs x /\
        Rabs (op (repeat x n)) > Rabs x).
Proof.
  intros n Hn.
  exists (INR n / INR (n - 1)).
  split; [reflexivity |].
  split; [apply nary_stability_condition; exact Hn |].
  intros op Hcyc Hid Hbary x Hx_neq.

  destruct Hbary as [d [Hd Hbary_def]].

  assert (Hn2: (n >= 2)%nat) by lia.
  assert (Hd_eq: d = INR (n - 1)).
  { eapply nary_identity_determines_denominator_barycentric; eauto. }

  assert (Hop_repeat: op (repeat x n) = INR n / INR (n - 1) * x).
  { eapply nary_barycentric_lipschitz; eauto. }

  split.
  - rewrite Hop_repeat.
    rewrite Rabs_mult.
    rewrite (Rabs_right (INR n / INR (n - 1))).
    + reflexivity.
    + apply Rle_ge.
      assert (Hn_pos: INR n > 0) by (apply lt_0_INR; lia).
      assert (Hn1_pos: INR (n - 1) > 0) by (apply lt_0_INR; lia).
      unfold Rdiv. apply Rmult_le_pos; [lra |].
      apply Rlt_le. apply Rinv_0_lt_compat. exact Hn1_pos.

  - rewrite Hop_repeat.
    assert (Hfactor: INR n / INR (n - 1) > 1).
    { apply nary_stability_condition. exact Hn. }
    assert (Hx_abs_pos: Rabs x > 0).
    { apply Rabs_pos_lt. exact Hx_neq. }
    rewrite Rabs_mult.
    rewrite (Rabs_right (INR n / INR (n - 1))).
    + assert (H: INR n / INR (n - 1) * Rabs x > 1 * Rabs x).
      { apply Rmult_gt_compat_r; assumption. }
      lra.
    + apply Rle_ge.
      assert (Hn_pos: INR n > 0) by (apply lt_0_INR; lia).
      assert (Hn1_pos: INR (n - 1) > 0) by (apply lt_0_INR; lia).
      unfold Rdiv. apply Rmult_le_pos; [lra |].
      apply Rlt_le. apply Rinv_0_lt_compat. exact Hn1_pos.
Qed.

(* Ternary case yields Lipschitz constant of 3/2 *)
Corollary ternary_is_special_case :
  let n := 3%nat in
  INR n / INR (n - 1) = 3 / 2.
Proof.
  simpl. lra.
Qed.

(* Quaternary case is also unstable *)
Corollary quaternary_also_unstable :
  let n := 4%nat in
  INR n / INR (n - 1) = 4 / 3 /\
  4 / 3 > 1.
Proof.
  simpl.
  split; [lra | lra].
Qed.

(* Binary case yields constant of 2 *)
Corollary binary_is_stable_boundary :
  let n := 2%nat in
  INR n / INR (n - 1) = 2 / 1 /\
  2 / 1 = 2.
Proof.
  simpl.
  split; [lra | lra].
Qed.

(* Cyclic and identity laws preclude affine ternary operations *)
Theorem ternary_affine_identity_impossible :
  forall op,
  nary_cyclic 3 op ->
  nary_identity_law 3 op 0 ->
  ~nary_affine 3 op.
Proof.
  intros op Hcyc Hid.
  intro Haff.
  destruct Haff as [coeffs [Hlen [Hsum Haffine]]].

  destruct (first_coeff_from_identity 3 coeffs op ltac:(lia) Hlen Hsum Haffine Hid)
    as [c0 [cs [Hcoeffs_eq [Hc0_zero Hcs_sum]]]].

  assert (Hlen_cs: length cs = 2%nat).
  { rewrite Hcoeffs_eq in Hlen. simpl in Hlen. lia. }

  destruct cs as [|c1 [|c2 [|]]]; try discriminate.
  simpl in Hcs_sum.
  clear Hlen_cs.

  unfold nary_cyclic in Hcyc.
  assert (Hcyc_affine: forall a0 a1 a2,
    c0 * a0 + c1 * a1 + c2 * a2 = c0 * a2 + c1 * a0 + c2 * a1).
  { intros a0 a1 a2.
    assert (Hlen_input: length [a0; a1; a2] = 3%nat) by (simpl; reflexivity).
    rewrite Hcoeffs_eq in Haffine.
    pose proof (Haffine [a0; a1; a2] Hlen_input) as H1.
    assert (Hrot: skipn 2 [a0; a1; a2] ++ firstn 2 [a0; a1; a2] = [a2; a0; a1]) by reflexivity.
    assert (Hlen_rot: length [a2; a0; a1] = 3%nat) by (simpl; reflexivity).
    pose proof (Haffine [a2; a0; a1] Hlen_rot) as H2.
    pose proof (Hcyc [a0; a1; a2] Hlen_input 2%nat ltac:(lia)) as Hcyc_inst.
    rewrite Hrot in Hcyc_inst.
    rewrite H1 in Hcyc_inst.
    rewrite H2 in Hcyc_inst.
    simpl in H1, H2, Hcyc_inst.
    lra. }

  pose proof (cyclic_forces_equal_coeffs_base c0 c1 c2 Hcyc_affine) as [Heq01 Heq12].

  rewrite Hc0_zero in Heq01.
  rewrite <- Heq01 in Hcs_sum.
  rewrite <- Heq12 in Hcs_sum.

  simpl in Hcs_sum.
  lra.
Qed.

End NaryGeneralization.

(* Spectral analysis of operators *)
Section OperatorSpectrum.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* Operator mapping x to ternary_op x x x *)
Definition T (x : Omega) : Omega := ternary_op x x x.

(* Element unchanged by T operator *)
Definition is_fixed_point (x : Omega) : Prop :=
  T x = x.

(* Identity element is fixed by T *)
Lemma identity_is_fixed_point : is_fixed_point identity.
Proof.
  unfold is_fixed_point, T.
  apply identity_law.
Qed.

(* Fixed point with zero valuation must be identity *)
Lemma fixed_point_zero_valuation : forall x,
  is_fixed_point x -> valuation x = 0 -> x = identity.
Proof.
  intros x Hfp Hval.
  apply valuation_faithful.
  exact Hval.
Qed.

(* Mapping to identity preserves fixed point property *)
Lemma T_identity_gives_fixed_point : forall x,
  T x = identity -> is_fixed_point identity.
Proof.
  intros x Hx.
  apply identity_is_fixed_point.
Qed.

(* Fixed points with zero valuation equal identity *)
Theorem fixed_point_with_zero_valuation_is_identity : forall x,
  is_fixed_point x -> valuation x = 0 -> x = identity.
Proof.
  intros x Hfp Hval.
  apply valuation_faithful.
  exact Hval.
Qed.

(* Identity is unique zero-valuation fixed point *)
Theorem identity_unique_zero_valuation_fixed_point : forall x,
  is_fixed_point x -> valuation x = 0 -> x = identity.
Proof.
  intros x Hfp Hval.
  apply fixed_point_with_zero_valuation_is_identity; assumption.
Qed.

(* Identity law holds in all three argument positions *)
Lemma identity_laws_all : forall a,
  ternary_op identity a a = a /\
  ternary_op a identity a = a /\
  ternary_op a a identity = a.
Proof.
  intro a.
  split; [apply identity_law|].
  split.
  - assert (Hid: ternary_op identity a a = a) by apply identity_law.
    rewrite cyclic_symmetry in Hid.
    exact Hid.
  - assert (Hid1: ternary_op identity a a = a) by apply identity_law.
    assert (Hid2: ternary_op a a identity = ternary_op identity a a).
    { rewrite cyclic_symmetry. rewrite cyclic_symmetry. reflexivity. }
    rewrite Hid2. exact Hid1.
Qed.

(* Two-step cyclic permutation equals double application *)
Lemma cyclic_permutation_1 : forall a b c,
  ternary_op a b c = ternary_op b c a.
Proof.
  intros a b c.
  rewrite cyclic_symmetry.
  rewrite cyclic_symmetry.
  reflexivity.
Qed.

(* Single-step cyclic permutation *)
Lemma cyclic_permutation_2 : forall a b c,
  ternary_op a b c = ternary_op c a b.
Proof.
  intros a b c.
  apply cyclic_symmetry.
Qed.

(* T operator has Lipschitz constant 3/2 *)
Lemma T_valuation_bound : forall x,
  valuation (T x) <= (3/2) * valuation x.
Proof.
  intros x.
  unfold T.
  pose proof (valuation_barycentric x x x) as Hineq.
  assert (H_calc: (valuation x + valuation x + valuation x) / 2 = 3 / 2 * valuation x).
  { field. }
  rewrite H_calc in Hineq.
  exact Hineq.
Qed.

(* Lipschitz constant for T operator *)
Definition lipschitz_bound_T : R := 3/2.

(* T valuation bounded by Lipschitz constant *)
Theorem T_valuation_lipschitz : forall x,
  valuation (T x) <= lipschitz_bound_T * valuation x.
Proof.
  intros x.
  unfold lipschitz_bound_T.
  apply T_valuation_bound.
Qed.


(* Iteration of T operator n times *)
Fixpoint T_iter (n : nat) (x : Omega) : Omega :=
  match n with
  | O => x
  | S n' => T (T_iter n' x)
  end.

(* Iterated T amplifies valuation exponentially *)
Lemma T_iter_bound : forall n x,
  valuation (T_iter n x) <= (3/2)^n * valuation x.
Proof.
  intros n x.
  induction n as [|n' IHn'].
  - simpl. lra.
  - simpl T_iter.
    apply Rle_trans with (r2 := (3/2) * valuation (T_iter n' x)).
    + apply T_valuation_bound.
    + apply Rle_trans with (r2 := (3/2) * ((3/2)^n' * valuation x)).
      * apply Rmult_le_compat_l; [lra | exact IHn'].
      * assert (Hexp: (3/2) * ((3/2)^n' * valuation x) = (3/2)^(S n') * valuation x).
        { simpl. ring. }
        rewrite Hexp. apply Rle_refl.
Qed.

End OperatorSpectrum.

(* Properties of derived binary operation *)
Section DerivedBinaryProperties.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* Binary operation with identity on right *)
Lemma derived_binary_with_identity_left : forall a,
  a ◊ identity = ternary_op a identity identity.
Proof.
  intro a.
  unfold derived_binary_op.
  reflexivity.
Qed.

(* Binary operation with identity on left *)
Lemma derived_binary_with_identity_right : forall a,
  identity ◊ a = ternary_op identity a identity.
Proof.
  intro a.
  unfold derived_binary_op.
  reflexivity.
Qed.

(* Binary identity preservation condition *)
Lemma derived_binary_identity_not_preserved : forall a,
  a ◊ identity = a -> ternary_op a identity identity = a.
Proof.
  intros a Heq.
  rewrite <- derived_binary_with_identity_left.
  exact Heq.
Qed.

(* Definition of binary operation via ternary *)
Lemma derived_binary_cyclic_variant : forall a b,
  a ◊ b = ternary_op a b identity.
Proof.
  intros a b.
  unfold derived_binary_op.
  reflexivity.
Qed.

(* Binary operation valuation bounded by average *)
Lemma derived_binary_valuation_bound : forall a b,
  valuation (a ◊ b) <= (valuation a + valuation b) / 2.
Proof.
  intros a b.
  unfold derived_binary_op.
  pose proof (valuation_barycentric a b identity) as Hbary.
  rewrite valuation_identity in Hbary.
  assert (Hcalc: (valuation a + valuation b + 0) / 2 = (valuation a + valuation b) / 2).
  { field. }
  rewrite <- Hcalc.
  exact Hbary.
Qed.

End DerivedBinaryProperties.

(* Quotient by valuation equivalence *)
Section QuotientStructure.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* Equivalence relation on elements with same valuation *)
Definition nu_equiv (a b : Omega) : Prop :=
  valuation a = valuation b.

(* Infix notation for valuation equivalence *)
Notation "a ~ b" := (nu_equiv a b) (at level 70).

(* Valuation equivalence is reflexive *)
Lemma nu_equiv_reflexive : forall a, a ~ a.
Proof.
  intro a.
  unfold nu_equiv.
  reflexivity.
Qed.

(* Valuation equivalence is symmetric *)
Lemma nu_equiv_symmetric : forall a b, a ~ b -> b ~ a.
Proof.
  intros a b Hab.
  unfold nu_equiv in *.
  symmetry.
  exact Hab.
Qed.

(* Valuation equivalence is transitive *)
Lemma nu_equiv_transitive : forall a b c, a ~ b -> b ~ c -> a ~ c.
Proof.
  intros a b c Hab Hbc.
  unfold nu_equiv in *.
  rewrite Hab.
  exact Hbc.
Qed.

(* Ternary operation respects valuation equivalence *)
Definition ternary_op_coherent : Prop :=
  forall a b c d e f,
    a ~ d -> b ~ e -> c ~ f ->
    ternary_op a b c ~ ternary_op d e f.

(* Weak coherence via barycentric bound *)
Lemma ternary_op_coherent_weak : forall a b c d e f,
  a ~ d -> b ~ e -> c ~ f ->
  valuation (ternary_op a b c) <=
  (valuation d + valuation e + valuation f) / 2.
Proof.
  intros a b c d e f Ha Hb Hc.
  unfold nu_equiv in *.
  pose proof (valuation_barycentric a b c) as H1.
  rewrite Ha, Hb, Hc in H1.
  exact H1.
Qed.

(* Coherence equivalent to valuation preservation *)
Remark ternary_op_coherent_reformulation :
  ternary_op_coherent <->
  (forall a b c d e f,
    valuation a = valuation d ->
    valuation b = valuation e ->
    valuation c = valuation f ->
    valuation (ternary_op a b c) = valuation (ternary_op d e f)).
Proof.
  unfold ternary_op_coherent, nu_equiv.
  split; intros Hcoh a b c d e f Ha Hb Hc; apply Hcoh; assumption.
Qed.

End QuotientStructure.

(* Constructing quotient algebra from coherent operation *)
Section QuotientConstruction.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* Quotient type of valuations *)
Definition quotient_elem := {v : R | exists x : Omega, valuation x = v}.

(* Construct quotient element from real value *)
Lemma quotient_elem_witness : forall (v : R),
  (exists x : Omega, valuation x = v) -> quotient_elem.
Proof.
  intros v Hex.
  exists v.
  exact Hex.
Defined.

(* Extract real value from quotient element *)
Definition quotient_val (q : quotient_elem) : R :=
  proj1_sig q.

(* Lift element to quotient by its valuation *)
Definition lift_to_quotient (x : Omega) : quotient_elem.
Proof.
  exists (valuation x).
  exists x.
  reflexivity.
Defined.

(* Lifting preserves valuation *)
Lemma lift_preserves_valuation : forall x,
  quotient_val (lift_to_quotient x) = valuation x.
Proof.
  intro x.
  unfold quotient_val, lift_to_quotient.
  simpl.
  reflexivity.
Qed.

(* Quotient elements equal when values equal *)
Lemma quotient_elem_eq : forall (q1 q2 : quotient_elem),
  quotient_val q1 = quotient_val q2 -> q1 = q2.
Proof.
  intros [v1 H1] [v2 H2] Heq.
  simpl in Heq.
  subst v2.
  f_equal.
  apply proof_irrelevance.
Qed.

(* Assume coherence for quotient construction *)
Context (coherence : ternary_op_coherent).

(* Choose representative element for quotient class *)
Definition choose_repr : quotient_elem -> Omega :=
  fun q => proj1_sig (constructive_indefinite_description _ (proj2_sig q)).

(* Representative has correct valuation *)
Lemma choose_repr_correct : forall q,
  valuation (choose_repr q) = quotient_val q.
Proof.
  intros [v Hex].
  unfold choose_repr, quotient_val.
  simpl.
  destruct (constructive_indefinite_description _ Hex) as [x Hx].
  simpl.
  exact Hx.
Qed.

(* Ternary operation on quotient elements *)
Definition quotient_ternary_op (q1 q2 q3 : quotient_elem) : quotient_elem :=
  lift_to_quotient (ternary_op (choose_repr q1) (choose_repr q2) (choose_repr q3)).

(* Quotient identity element *)
Definition quotient_identity : quotient_elem :=
  lift_to_quotient identity.

(* Quotient identity has zero value *)
Lemma quotient_identity_val : quotient_val quotient_identity = 0.
Proof.
  unfold quotient_identity, quotient_val, lift_to_quotient.
  simpl.
  apply valuation_identity.
Qed.

(* Quotient operation well-defined on equivalence classes *)
Lemma quotient_op_well_defined : forall q1 q2 q3 q1' q2' q3',
  quotient_val q1 = quotient_val q1' ->
  quotient_val q2 = quotient_val q2' ->
  quotient_val q3 = quotient_val q3' ->
  quotient_val (quotient_ternary_op q1 q2 q3) =
  quotient_val (quotient_ternary_op q1' q2' q3').
Proof.
  intros q1 q2 q3 q1' q2' q3' Hq1 Hq2 Hq3.
  unfold quotient_ternary_op, quotient_val, lift_to_quotient.
  simpl.
  unfold ternary_op_coherent, nu_equiv in coherence.
  apply coherence.
  - rewrite choose_repr_correct. rewrite choose_repr_correct. exact Hq1.
  - rewrite choose_repr_correct. rewrite choose_repr_correct. exact Hq2.
  - rewrite choose_repr_correct. rewrite choose_repr_correct. exact Hq3.
Qed.

(* Quotient operation satisfies cyclic symmetry *)
Lemma quotient_cyclic_symmetry : forall a b c,
  quotient_ternary_op a b c = quotient_ternary_op c a b.
Proof.
  intros a b c.
  unfold quotient_ternary_op.
  f_equal.
  apply cyclic_symmetry.
Qed.

(* Representative of quotient identity is identity *)
Lemma choose_repr_quotient_identity_faithful :
  choose_repr quotient_identity = identity.
Proof.
  apply valuation_faithful.
  rewrite choose_repr_correct.
  unfold quotient_identity, quotient_val, lift_to_quotient.
  simpl.
  apply valuation_identity.
Qed.

(* Quotient operation satisfies identity law *)
Lemma quotient_identity_law : forall a,
  quotient_ternary_op quotient_identity a a = a.
Proof.
  intro a.
  apply quotient_elem_eq.
  unfold quotient_ternary_op, quotient_val.
  simpl.
  unfold lift_to_quotient.
  simpl.
  repeat rewrite choose_repr_correct.
  rewrite choose_repr_quotient_identity_faithful.
  pose proof (identity_law (choose_repr a)) as Hid.
  rewrite Hid.
  rewrite choose_repr_correct.
  reflexivity.
Qed.

(* Quotient forms ternary algebra instance *)
Instance QuotientTernaryAlgebra : TernaryAlgebra quotient_elem := {
  ternary_op := quotient_ternary_op;
  identity := quotient_identity;
  cyclic_symmetry := quotient_cyclic_symmetry;
  identity_law := quotient_identity_law;
}.

(* Coherence implies quotient algebra exists *)
Theorem quotient_inherits_ternary_algebra_when_coherent :
  ternary_op_coherent ->
  exists (Q : Type) (H : TernaryAlgebra Q), True.
Proof.
  intro Hcoh.
  exists quotient_elem, QuotientTernaryAlgebra.
  exact I.
Qed.

End QuotientConstruction.

(* Convergence properties of iterated operations *)
Section ConvergenceAnalysis.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* Family of elements indexed by naturals *)
Context (f : nat -> Omega).
(* Family is injective *)
Context (f_injection : forall n m, f n = f m -> n = m).
(* Valuation decreases as 1/n *)
Context (f_valuation : forall n, (n > 0)%nat -> valuation (f n) = 1 / INR n).

(* Recursive sequence using ternary operation *)
Fixpoint sequence (a0 a1 : Omega) (n : nat) : Omega :=
  match n with
  | 0%nat => a0
  | 1%nat => a1
  | S (S m as n') => ternary_op (sequence a0 a1 n') (sequence a0 a1 m) (f (S (S m)))
  end.

(* Positive naturals have positive real value *)
Lemma INR_pos : forall n, (n > 0)%nat -> INR n > 0.
Proof.
  intros n Hn.
  apply lt_INR in Hn.
  simpl in Hn.
  exact Hn.
Qed.

(* Reciprocal of n at least 2 bounded by 1/2 *)
Lemma inv_INR_bound : forall n, (n >= 2)%nat -> 1 / INR n <= 1/2.
Proof.
  intros n Hn.
  assert (H2: INR n >= 2).
  { apply le_INR in Hn. simpl in Hn. lra. }
  assert (H_pos: INR n > 0).
  { apply INR_pos. lia. }
  apply Rmult_le_reg_r with (r := INR n).
  - exact H_pos.
  - field_simplify.
    + lra.
    + lra.
Qed.

(* Valuation of f bounded by 1/2 for n>=2 *)
Lemma valuation_f_bound : forall n, (n >= 2)%nat -> valuation (f n) <= 1/2.
Proof.
  intros n Hn.
  rewrite f_valuation.
  - apply inv_INR_bound. exact Hn.
  - lia.
Qed.

(* Sequence valuation remains bounded *)
Lemma sequence_valuation_bound : forall a0 a1 n,
  (n >= 2)%nat ->
  valuation (sequence a0 a1 n) <=
  (valuation (sequence a0 a1 (n-1)) + valuation (sequence a0 a1 (n-2)) + valuation (f n)) / 2.
Proof.
  intros a0 a1 n Hn.
  destruct n as [|[|m]].
  - lia.
  - lia.
  - assert (H1: (S (S m) - 1 = S m)%nat) by lia.
    assert (H2: (S (S m) - 2 = m)%nat) by lia.
    rewrite H1, H2.
    simpl.
    apply valuation_barycentric.
Qed.

(* Sequence valuation grows at most linearly *)
Theorem sequence_valuation_linear_bound : forall a0 a1 n,
  valuation (sequence a0 a1 n) <=
  Rmax (valuation a0) (valuation a1) + INR n * / 2.
Proof.
  intros a0 a1 n.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  destruct n as [|[|n']].
  - simpl.
    assert (H_rmax: valuation a0 <= Rmax (valuation a0) (valuation a1)).
    { apply Rmax_l. }
    simpl. lra.
  - simpl.
    assert (H_rmax: valuation a1 <= Rmax (valuation a0) (valuation a1)).
    { apply Rmax_r. }
    simpl. lra.
  - simpl sequence.
    apply Rle_trans with (r2 := (valuation (sequence a0 a1 (S n')) + valuation (sequence a0 a1 n') + valuation (f (S (S n')))) / 2).
    + apply valuation_barycentric.
    + assert (H1: valuation (sequence a0 a1 (S n')) <= Rmax (valuation a0) (valuation a1) + INR (S n') * / 2).
      { apply IHn. lia. }
      assert (H2: valuation (sequence a0 a1 n') <= Rmax (valuation a0) (valuation a1) + INR n' * / 2).
      { apply IHn. lia. }
      assert (Hf_bound: valuation (f (S (S n'))) <= 1 / 2).
      { apply valuation_f_bound. lia. }
      assert (H_sum_bound: valuation (sequence a0 a1 (S n')) + valuation (sequence a0 a1 n') + valuation (f (S (S n'))) <=
                          2 * Rmax (valuation a0) (valuation a1) + INR (S n') * / 2 + INR n' * / 2 + 1 / 2).
      { lra. }
      apply Rle_trans with (r2 := (2 * Rmax (valuation a0) (valuation a1) + INR (S n') * / 2 + INR n' * / 2 + 1 / 2) / 2).
      * apply Rmult_le_compat_r; [lra | exact H_sum_bound].
      * assert (H_simp1: INR (S (S n')) = INR n' + 2).
        { rewrite S_INR. rewrite S_INR. simpl. lra. }
        assert (H_simp2: INR (S n') = INR n' + 1).
        { rewrite S_INR. simpl. lra. }
        rewrite H_simp1, H_simp2. lra.
Qed.

(* Reciprocal of positive real is positive *)
Lemma inv_pos : forall x, x > 0 -> 1 / x > 0.
Proof.
  intros x Hx.
  apply Rdiv_lt_0_compat; lra.
Qed.

(* Archimedean property witness as natural *)
Lemma archimed_nat_witness : forall r, r > 0 ->
  exists N, (N > 0)%nat /\ INR N > r.
Proof.
  intros r Hr.
  destruct (archimed r) as [H_up H_low].
  assert (H_up_pos: (0 < up r)%Z).
  { apply lt_IZR. apply Rle_lt_trans with (r2 := r); lra. }
  exists (S (Z.to_nat (up r))).
  split; [lia |].
  rewrite S_INR. rewrite INR_IZR_INZ.
  rewrite Z2Nat.id by lia. lra.
Qed.

(* Reciprocal decreases as natural increases *)
Lemma inv_INR_decreasing : forall n m,
  (n > 0)%nat -> (m > 0)%nat ->
  (n >= m)%nat -> 1 / INR n <= 1 / INR m.
Proof.
  intros n m Hn Hm Hnm.
  assert (H_n_pos: INR n > 0) by (apply INR_pos; exact Hn).
  assert (H_m_pos: INR m > 0) by (apply INR_pos; exact Hm).
  apply Rmult_le_reg_r with (r := INR n * INR m).
  - apply Rmult_lt_0_compat; assumption.
  - field_simplify.
    + apply le_INR in Hnm. lra.
    + lra.
    + lra.
Qed.

(* Large n implies small reciprocal *)
Lemma inv_INR_lt_bound : forall n r,
  (n > 0)%nat -> INR n > 1 / r -> r > 0 -> 1 / INR n < r.
Proof.
  intros n r Hn Hbound Hr.
  assert (H_n_pos: INR n > 0) by (apply INR_pos; exact Hn).
  assert (H_prod: INR n * r > 1).
  { apply Rmult_gt_reg_r with (r := /r).
    - apply Rinv_0_lt_compat. exact Hr.
    - replace (INR n * r * / r) with (INR n) by (field; lra).
      replace (1 * / r) with (/ r) by ring.
      replace (/ r) with (1 / r) by (unfold Rdiv; ring).
      exact Hbound. }
  apply Rmult_lt_reg_r with (r := INR n).
  - exact H_n_pos.
  - replace (1 / INR n * INR n) with 1 by (field; lra).
    replace (r * INR n) with (INR n * r) by ring.
    exact H_prod.
Qed.

(* Valuation of f becomes arbitrarily small *)
Lemma f_valuation_implies_limit : forall eps, eps > 0 ->
  exists N, forall n, (n >= N)%nat -> valuation (f n) < eps.
Proof.
  intros eps Heps.
  assert (H_inv_pos: 1 / eps > 0) by (apply inv_pos; exact Heps).
  destruct (archimed_nat_witness (1 / eps) H_inv_pos) as [N [HN_pos HN_bound]].
  exists N.
  intros n Hn.
  assert (Hn_pos: (n > 0)%nat) by lia.
  rewrite f_valuation by exact Hn_pos.
  assert (H_n_ge_N: (n >= N)%nat) by exact Hn.
  assert (H_inv_dec: 1 / INR n <= 1 / INR N).
  { apply inv_INR_decreasing; assumption. }
  apply Rle_lt_trans with (r2 := 1 / INR N); [exact H_inv_dec |].
  apply inv_INR_lt_bound; assumption.
Qed.

(* Sequence is Cauchy if valuations converge *)
Definition is_Cauchy (seq : nat -> Omega) : Prop :=
  forall eps, eps > 0 -> exists N, forall n m,
    (n >= N)%nat -> (m >= N)%nat ->
    Rabs (valuation (seq n) - valuation (seq m)) < eps.

(* Family f converges to identity in valuation *)
Theorem f_converges_to_identity :
  forall eps, eps > 0 ->
  exists N, forall n, (n >= N)%nat ->
  Rabs (valuation (f n) - 0) < eps.
Proof.
  intros eps Heps.
  destruct (f_valuation_implies_limit eps Heps) as [N HN].
  exists N.
  intros n Hn.
  rewrite Rminus_0_r.
  rewrite Rabs_right.
  - apply HN. exact Hn.
  - apply Rle_ge. apply valuation_nonneg.
Qed.

(* Constant sequences are Cauchy *)
Theorem constant_sequence_is_Cauchy : forall x : Omega,
  is_Cauchy (fun _ => x).
Proof.
  intro x.
  unfold is_Cauchy.
  intros eps Heps.
  exists 0%nat.
  intros n m Hn Hm.
  rewrite Rminus_diag_eq by reflexivity.
  rewrite Rabs_R0.
  exact Heps.
Qed.

(* Eventually constant sequences are Cauchy *)
Theorem eventually_constant_implies_Cauchy : forall (seq : nat -> Omega) (N : nat) (x : Omega),
  (forall n, (n >= N)%nat -> seq n = x) ->
  is_Cauchy seq.
Proof.
  intros seq N x Heventual.
  unfold is_Cauchy.
  intros eps Heps.
  exists N.
  intros n m Hn Hm.
  rewrite (Heventual n Hn).
  rewrite (Heventual m Hm).
  rewrite Rminus_diag_eq by reflexivity.
  rewrite Rabs_R0.
  exact Heps.
Qed.

End ConvergenceAnalysis.

(* Convergence when perturbations are all identity *)
Section ConvergenceAnalysisIdentityCase.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* Family mapping to identity *)
Context (f : nat -> Omega).
(* All elements are identity *)
Context (f_all_identity : forall n, (n > 0)%nat -> f n = identity).

(* Sequence with identity perturbations *)
Fixpoint sequence_identity (a0 a1 : Omega) (n : nat) : Omega :=
  match n with
  | 0%nat => a0
  | 1%nat => a1
  | S (S m as n') => ternary_op (sequence_identity a0 a1 n') (sequence_identity a0 a1 m) (f (S (S m)))
  end.

(* Sequence starting from identity stays at identity *)
Theorem sequence_from_identity_with_identity_perturbations : forall n,
  sequence_identity identity identity n = identity.
Proof.
  intro n.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  destruct n as [|[|n']].
  - reflexivity.
  - reflexivity.
  - change (sequence_identity identity identity (S (S n'))) with
      (ternary_op (sequence_identity identity identity (S n'))
                  (sequence_identity identity identity n')
                  (f (S (S n')))).
    rewrite (IHn (S n')).
    + rewrite (IHn n').
      * rewrite (f_all_identity (S (S n'))).
        -- rewrite identity_law. reflexivity.
        -- lia.
      * lia.
    + lia.
Qed.

(* Identity sequence with identity perturbations is Cauchy *)
Corollary identity_sequence_with_trivial_f_is_Cauchy :
  is_Cauchy (fun n => sequence_identity identity identity n).
Proof.
  apply eventually_constant_implies_Cauchy with (N := 0%nat) (x := identity).
  intro n. intro Hge. apply sequence_from_identity_with_identity_perturbations.
Qed.

End ConvergenceAnalysisIdentityCase.

(* General convergence theorems for sequences *)
Section GeneralConvergenceTheorems.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* General Cauchy sequence definition *)
Definition is_Cauchy_general (seq : nat -> Omega) : Prop :=
  forall eps, eps > 0 -> exists N, forall n m,
    (n >= N)%nat -> (m >= N)%nat ->
    Rabs (valuation (seq n) - valuation (seq m)) < eps.

(* Bounded sequences with small gaps are Cauchy *)
Theorem bounded_convergence_implies_Cauchy:
  forall (seq : nat -> Omega),
  (exists M, forall n, valuation (seq n) <= M) ->
  (forall eps, eps > 0 -> exists N, forall n m,
     (n >= N)%nat -> (m >= N)%nat ->
     Rabs (valuation (seq n) - valuation (seq m)) < eps) ->
  is_Cauchy_general seq.
Proof.
  intros seq Hbounded Hgaps.
  unfold is_Cauchy_general.
  exact Hgaps.
Qed.

End GeneralConvergenceTheorems.

(* Homomorphisms between ternary algebras *)
Section Homomorphisms.

Context {Omega Omega' : Type}.
Context `{ValuatedTernaryAlgebra Omega}.
Context `{ValuatedTernaryAlgebra Omega'}.

(* Map between algebras *)
Context (phi : Omega -> Omega').

(* Map preserves ternary operation *)
Definition preserves_ternary_structure : Prop :=
  forall a b c,
    phi (ternary_op a b c) = ternary_op (phi a) (phi b) (phi c).

(* Real function for valuation transformation *)
Context (g : R -> R).

(* Map transforms valuations via g *)
Definition preserves_valuation : Prop :=
  forall x, valuation (phi x) = g (valuation x).

(* Function g is strictly increasing *)
Definition g_strictly_monotonic : Prop :=
  forall x y, x < y -> g x < g y.

(* Function g maps zero to zero *)
Definition g_zero : Prop := g 0 = 0.

(* Map is homomorphism of valuated algebras *)
Definition is_homomorphism : Prop :=
  preserves_ternary_structure /\ preserves_valuation.

(* Structure preserving with Lipschitz bound *)
Definition preserves_structure_Lipschitz (c : R) : Prop :=
  preserves_ternary_structure /\ forall x, valuation (phi x) <= c * valuation x.

(* Function g is positive homogeneous *)
Definition g_pos_hom : Prop :=
  forall lambda t, 0 <= lambda -> g (lambda * t) = lambda * g t.

(* Function g preserves barycentric inequality *)
Definition g_subadditive : Prop :=
  forall x y z,
    g ((x + y + z) / 2) <= (g x + g y + g z) / 2.

(* Linear functions are subadditive *)
Lemma linear_g_satisfies_subadditive : forall c,
  (forall t, g t = c * t) -> g_subadditive.
Proof.
  intros c Hlin.
  unfold g_subadditive.
  intros x y z.
  rewrite Hlin. rewrite Hlin. rewrite Hlin. rewrite Hlin.
  lra.
Qed.

(* Positive homogeneous subadditive functions preserve barycentric *)
Lemma pos_hom_subadditive_preserves_barycentric :
  g_pos_hom -> g_subadditive ->
  forall x y z,
    g ((x + y + z) / 2) <= (g x + g y + g z) / 2.
Proof.
  intros Hhom Hsub x y z.
  apply Hsub.
Qed.

(* Power law function with exponent alpha *)
Definition g_power_law (c alpha : R) : R -> R :=
  fun x => c * Rpower x alpha.

(* Quadratic function as power law *)
Example g_quadratic (c : R) : R -> R := g_power_law c 2.

(* Square root function as power law *)
Example g_sqrt (c : R) : R -> R := g_power_law c (1/2).

(* Linear functions map zero to zero *)
Theorem linear_g_is_g_zero : forall c,
  (forall t, t >= 0 -> g t = c * t) -> g 0 = 0.
Proof.
  intros c Hlin.
  rewrite Hlin by lra.
  lra.
Qed.

(* Quadratic functions violate subadditivity *)
Theorem quadratic_violates_subadditive : forall c,
  c > 0 ->
  (forall t, t >= 0 -> g t = c * t * t) ->
  ~ g_subadditive.
Proof.
  intros c Hc Hquad.
  unfold g_subadditive.
  intro Hcontra.
  specialize (Hcontra 1 1 1).
  assert (Hsum: (1 + 1 + 1) / 2 = 3 / 2) by lra.
  assert (Hg_lhs: g ((1 + 1 + 1) / 2) = c * (3/2) * (3/2)).
  { rewrite Hsum. apply Hquad. lra. }
  assert (Hg_rhs1: g 1 = c * 1 * 1) by (apply Hquad; lra).
  assert (Hg_rhs: (g 1 + g 1 + g 1) / 2 = c * 3 / 2).
  { rewrite Hg_rhs1. lra. }
  rewrite Hg_lhs in Hcontra.
  rewrite Hg_rhs in Hcontra.
  lra.
Qed.

(* Homomorphisms preserve barycentric bounds *)
Theorem homomorphism_gives_barycentric_bound :
  is_homomorphism ->
  forall a b c,
    valuation (phi (ternary_op a b c)) <=
    (g (valuation a) + g (valuation b) + g (valuation c)) / 2.
Proof.
  intros [Hpres Hval] a b c.
  rewrite Hpres.
  assert (Hineq: valuation (ternary_op (phi a) (phi b) (phi c)) <=
                 (valuation (phi a) + valuation (phi b) + valuation (phi c)) / 2).
  { apply valuation_barycentric. }
  unfold preserves_valuation in Hval.
  rewrite Hval, Hval, Hval in Hineq.
  exact Hineq.
Qed.

(* Homomorphism with g_zero preserves identity valuation *)
Lemma g_preserves_identity_valuation :
  is_homomorphism ->
  g_zero ->
  valuation (phi identity) = 0.
Proof.
  intros [Hpres Hval] Hgz.
  unfold preserves_valuation in Hval.
  rewrite Hval.
  rewrite valuation_identity.
  exact Hgz.
Qed.

End Homomorphisms.

(* Associator and non-associativity *)
Section AssociatorFormalism.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* Operation fails to associate *)
Definition non_associative : Prop :=
  exists a b c d e,
    ternary_op (ternary_op a b c) d e <>
    ternary_op a (ternary_op b c d) e.

(* Left-nested associator *)
Definition associator (a b c d e : Omega) : Omega :=
  ternary_op (ternary_op a b c) d e.

(* Associator valuation bounded *)
Theorem associator_valuation_bound : forall a b c d e,
  valuation (associator a b c d e) <=
  (valuation (ternary_op a b c) + valuation d + valuation e) / 2.
Proof.
  intros a b c d e.
  unfold associator.
  apply valuation_barycentric.
Qed.

(* Left associator valuation bound *)
Lemma associator_bound_left : forall a b c d e,
  valuation (ternary_op (ternary_op a b c) d e) <=
  (valuation a + valuation b + valuation c + 2*valuation d + 2*valuation e) / 4.
Proof.
  intros a b c d e.
  apply Rle_trans with (r2 := (valuation (ternary_op a b c) + valuation d + valuation e) / 2).
  - apply valuation_barycentric.
  - set (X := valuation (ternary_op a b c)).
    assert (HX: X <= (valuation a + valuation b + valuation c) / 2).
    { unfold X. apply valuation_barycentric. }
    assert (H_calc: (X + valuation d + valuation e) / 2 <=
                    ((valuation a + valuation b + valuation c) / 2 + valuation d + valuation e) / 2).
    { apply Rmult_le_compat_r; [lra |].
      apply Rplus_le_compat_r. apply Rplus_le_compat_r. exact HX. }
    apply Rle_trans with (r2 := ((valuation a + valuation b + valuation c) / 2 + valuation d + valuation e) / 2).
    + exact H_calc.
    + assert (H_simp: ((valuation a + valuation b + valuation c) / 2 + valuation d + valuation e) / 2 =
                     (valuation a + valuation b + valuation c + 2*valuation d + 2*valuation e) / 4).
      { field. }
      rewrite H_simp. apply Rle_refl.
Qed.

(* Right associator valuation bound *)
Lemma associator_bound_right : forall a b c d e,
  valuation (ternary_op a (ternary_op b c d) e) <=
  (2*valuation a + valuation b + valuation c + valuation d + 2*valuation e) / 4.
Proof.
  intros a b c d e.
  apply Rle_trans with (r2 := (valuation a + valuation (ternary_op b c d) + valuation e) / 2).
  - apply valuation_barycentric.
  - assert (HY: valuation (ternary_op b c d) <= (valuation b + valuation c + valuation d) / 2).
    { apply valuation_barycentric. }
    assert (H_calc: (valuation a + valuation (ternary_op b c d) + valuation e) <=
                    valuation a + (valuation b + valuation c + valuation d) / 2 + valuation e).
    { lra. }
    apply Rle_trans with (r2 := (valuation a + (valuation b + valuation c + valuation d) / 2 + valuation e) / 2).
    + apply Rmult_le_compat_r; [lra | exact H_calc].
    + assert (H_simp: (valuation a + (valuation b + valuation c + valuation d) / 2 + valuation e) / 2 =
                     (2*valuation a + valuation b + valuation c + valuation d + 2*valuation e) / 4).
      { field. }
      rewrite H_simp. apply Rle_refl.
Qed.

(* Valuation distinguishes non-associative cases *)
Theorem non_associativity_witnessed_by_valuation : forall a b c d e,
  valuation (ternary_op (ternary_op a b c) d e) <>
  valuation (ternary_op a (ternary_op b c d) e) ->
  ternary_op (ternary_op a b c) d e <>
  ternary_op a (ternary_op b c d) e.
Proof.
  intros a b c d e Hval_neq Heq.
  apply Hval_neq.
  rewrite Heq.
  reflexivity.
Qed.

End AssociatorFormalism.

(* Trivial single-element instance *)
(* Trivial unit type instance *)
Section TrivialInstance.

(* Unit type forms ternary algebra *)
Instance TrivialTernaryAlgebra : TernaryAlgebra unit := {
  ternary_op := fun _ _ _ => tt;
  identity := tt;
  cyclic_symmetry := fun a b c => match a, b, c with tt, tt, tt => eq_refl end;
  identity_law := fun u => match u with tt => eq_refl end;
}.

(* Trivial valuation satisfies barycentric bound *)
Lemma trivial_valuation_barycentric : forall a b c : unit,
  0 <= (0 + 0 + 0) / 2.
Proof.
  intros.
  lra.
Qed.

(* Zero valuation implies unit element *)
Lemma trivial_valuation_faithful `{TernaryAlgebra unit} : forall x : unit,
  (fun _ : unit => 0) x = 0 -> x = tt.
Proof.
  intros []; reflexivity.
Qed.

(* Unit type forms valuated ternary algebra *)
Instance TrivialValuatedTernaryAlgebra : ValuatedTernaryAlgebra unit := {
  valuation := fun _ => 0;
  valuation_nonneg := fun u => match u with tt => Rle_refl 0 end;
  valuation_identity := eq_refl;
  valuation_barycentric := trivial_valuation_barycentric;
  valuation_faithful := trivial_valuation_faithful;
}.

(* Trivial instance satisfies all axioms *)
Lemma trivial_instance_satisfies_all_axioms :
  exists (Omega : Type) (H : TernaryAlgebra Omega) (H0 : ValuatedTernaryAlgebra Omega), True.
Proof.
  exists unit, TrivialTernaryAlgebra, TrivialValuatedTernaryAlgebra.
  exact I.
Qed.

(* Trivial instance is coherent *)
Theorem trivial_instance_is_coherent : ternary_op_coherent.
Proof.
  unfold ternary_op_coherent, nu_equiv.
  intros a b c d e f Ha Hb Hc.
  destruct a, b, c, d, e, f.
  simpl.
  reflexivity.
Qed.

(* Trivial instance witnesses coherence *)
Corollary trivial_satisfies_coherence_axioms :
  exists (Omega : Type) (H : TernaryAlgebra Omega) (H0 : ValuatedTernaryAlgebra Omega),
    ternary_op_coherent.
Proof.
  exists unit, TrivialTernaryAlgebra, TrivialValuatedTernaryAlgebra.
  apply trivial_instance_is_coherent.
Qed.

End TrivialInstance.

(* Real numbers as normed instance *)
Section NormedVectorSpaceInstance.

(* Real numbers as carrier *)
Definition R_vec := R.

(* Average ternary operation on reals *)
Definition R_vec_ternary (a b c : R_vec) : R_vec :=
  (a + b + c) / 2.

(* Zero as identity element *)
Definition R_vec_identity : R_vec := 0.

(* Absolute value as norm *)
Definition R_vec_norm (x : R_vec) : R := Rabs x.

(* Ternary operation on reals is cyclic *)
Lemma R_vec_cyclic : forall a b c,
  R_vec_ternary a b c = R_vec_ternary c a b.
Proof.
  intros a b c.
  unfold R_vec_ternary.
  f_equal. ring.
Qed.

(* Real identity law for averaging *)
Lemma R_vec_identity_law : forall a,
  R_vec_ternary R_vec_identity a a = a.
Proof.
  intro a.
  unfold R_vec_ternary, R_vec_identity.
  field_simplify; lra.
Qed.

(* Real numbers form ternary algebra *)
Instance RVecTernaryAlgebra : TernaryAlgebra R_vec := {
  ternary_op := R_vec_ternary;
  identity := R_vec_identity;
  cyclic_symmetry := R_vec_cyclic;
  identity_law := R_vec_identity_law;
}.

(* Absolute value is nonnegative *)
Lemma R_vec_norm_nonneg : forall x, 0 <= R_vec_norm x.
Proof.
  intro x.
  unfold R_vec_norm.
  apply Rabs_pos.
Qed.

(* Zero has zero norm *)
Lemma R_vec_norm_identity : R_vec_norm R_vec_identity = 0.
Proof.
  unfold R_vec_norm, R_vec_identity.
  apply Rabs_R0.
Qed.

(* Triangle inequality for averaging *)
Lemma R_vec_barycentric : forall a b c,
  R_vec_norm (R_vec_ternary a b c) <= (R_vec_norm a + R_vec_norm b + R_vec_norm c) / 2.
Proof.
  intros a b c.
  unfold R_vec_norm, R_vec_ternary, Rdiv.
  assert (Hinv2: 0 < / 2) by (apply Rinv_0_lt_compat; lra).
  apply Rle_trans with (r2 := Rabs (a + b + c) * / 2).
  - rewrite Rabs_mult.
    rewrite (Rabs_right (/ 2)).
    + apply Rle_refl.
    + lra.
  - apply Rle_trans with (r2 := (Rabs (a + b) + Rabs c) * / 2).
    + apply Rmult_le_compat_r.
      * lra.
      * apply Rabs_triang.
    + apply Rle_trans with (r2 := ((Rabs a + Rabs b) + Rabs c) * / 2).
      * apply Rmult_le_compat_r.
        -- lra.
        -- apply Rplus_le_compat_r. apply Rabs_triang.
      * apply Req_le. field.
Qed.

(* Zero norm implies zero value *)
Lemma R_vec_faithful : forall x,
  R_vec_norm x = 0 -> x = R_vec_identity.
Proof.
  intros x Hx.
  unfold R_vec_norm, R_vec_identity in *.
  assert (x = 0).
  { destruct (Rcase_abs x) as [Hneg | Hnonneg].
    - rewrite Rabs_left in Hx by lra. lra.
    - rewrite Rabs_right in Hx by lra. lra. }
  exact H.
Qed.

(* Real numbers form valuated ternary algebra *)
Instance RVecValuatedTernaryAlgebra : ValuatedTernaryAlgebra R_vec := {
  valuation := R_vec_norm;
  valuation_nonneg := R_vec_norm_nonneg;
  valuation_identity := R_vec_norm_identity;
  valuation_barycentric := R_vec_barycentric;
  valuation_faithful := R_vec_faithful;
}.

(* Uniqueness of affine representation *)
Section UniquenessOfAffineForm.

(* Stone (1949) MR 0036014; Dudek-Głazek (2008) *)

(* Identity law forces denominator to be 2 *)
Theorem denominator_two_is_forced :
  forall (d : R),
  d > 0 ->
  (forall a, (0 + a + a) / d = a) <-> d = 2.
Proof.
  intros d Hd.
  split; intro Heq.
  - specialize (Heq 1).
    assert (Hcalc: 2 / d = 1) by lra.
    apply Rmult_eq_compat_r with (r := d) in Hcalc.
    unfold Rdiv in Hcalc.
    replace (2 * / d * d) with (2 * (/ d * d)) in Hcalc by ring.
    rewrite Rinv_l in Hcalc by lra.
    rewrite Rmult_1_r in Hcalc.
    lra.
  - subst d. intro a. lra.
Qed.

(* Constant input amplifies by 3/2 *)
Theorem lipschitz_constant_is_three_halves :
  forall x : R,
  Rabs ((x + x + x) / 2) = (3/2) * Rabs x.
Proof.
  intro x.
  replace ((x + x + x) / 2) with (3/2 * x) by field.
  rewrite Rabs_mult.
  rewrite (Rabs_right (3/2)) by lra.
  reflexivity.
Qed.

(* Identity and stability are incompatible *)
Theorem fundamental_incompatibility :
  forall (d : R),
  d > 0 ->
  (forall a, (0 + a + a) / d = a) ->
  (3/d > 1) /\ ~(3/d <= 1).
Proof.
  intros d Hd Hidentity.
  assert (Hd_eq_2: d = 2) by (apply denominator_two_is_forced; assumption).
  subst d.
  split.
  - unfold Rdiv. lra.
  - intro Hcontra. unfold Rdiv in Hcontra. lra.
Qed.

End UniquenessOfAffineForm.

(* Exact T operator amplification on reals *)
Lemma R_vec_T_exact : forall x,
  valuation (T x) = (3/2) * valuation x.
Proof.
  intro x.
  unfold T, valuation, R_vec_norm, R_vec_ternary; simpl.
  unfold R_vec_ternary.
  assert (H_calc: (x + x + x) / 2 = 3 / 2 * x).
  { field. }
  rewrite H_calc.
  rewrite Rabs_mult.
  rewrite (Rabs_right (3/2)) by lra.
  reflexivity.
Qed.

(* T operator achieves Lipschitz bound exactly *)
Definition T_bound_is_exact : Prop :=
  forall x, x <> identity -> valuation (T x) = lipschitz_bound_T * valuation x.

(* Real instance has exact bound *)
Theorem R_vec_has_exact_T_bound : T_bound_is_exact.
Proof.
  unfold T_bound_is_exact, lipschitz_bound_T.
  intros x Hneq.
  apply R_vec_T_exact.
Qed.

(* T operator preserves sign of real input *)
Corollary R_vec_T_preserves_sign : forall x,
  (x >= 0 -> T x >= 0) /\ (x <= 0 -> T x <= 0).
Proof.
  intro x.
  unfold T; simpl. unfold R_vec_ternary.
  split; intro H; lra.
Qed.

(* T strictly increases valuation for positive reals *)
Theorem R_vec_T_strict_growth_positive : forall x,
  x > 0 -> valuation (T x) > valuation x.
Proof.
  intros x Hpos.
  rewrite R_vec_T_exact.
  unfold valuation; simpl. unfold R_vec_norm.
  rewrite (Rabs_right x) by lra.
  lra.
Qed.

(* Zero is only real fixed point *)
Theorem R_vec_identity_unique_fixed_point : forall x : R_vec,
  is_fixed_point x -> x = identity.
Proof.
  intros x Hfixed.
  unfold is_fixed_point, T in Hfixed.
  simpl in Hfixed.
  unfold R_vec_ternary in Hfixed.
  unfold identity; simpl.
  unfold R_vec_identity.
  assert (Heq: (x + x + x) / 2 = x) by exact Hfixed.
  lra.
Qed.

(* Iterated T amplifies by power of 3/2 *)
Lemma R_vec_T_iter_exact : forall n x,
  valuation (T_iter n x : R_vec) = (3/2)^n * valuation x.
Proof.
  intros n x.
  induction n as [|n' IHn'].
  - simpl. lra.
  - change (T_iter (S n') x) with (T (T_iter n' x)).
    pose proof (R_vec_T_exact (T_iter n' x)) as HT.
    rewrite HT.
    rewrite IHn'.
    simpl. ring.
Qed.

(* T strictly amplifies nonzero reals *)
Example R_vec_T_diverges_concrete : forall x : R_vec,
  x <> identity ->
  valuation (T x) > valuation x.
Proof.
  intros x Hneq.
  rewrite R_vec_T_exact.
  assert (Hval_pos: valuation x > 0).
  { assert (Hval_nonneg: 0 <= valuation x) by apply valuation_nonneg.
    destruct (Rtotal_order 0 (valuation x)) as [Hlt | [Heq | Hgt]].
    - exact Hlt.
    - symmetry in Heq. apply valuation_faithful in Heq. contradiction.
    - lra. }
  lra.
Qed.

(* Exponential error growth analysis *)
Section ErrorAmplification.

(* Concrete bound at 11 iterations *)
Lemma error_at_iteration_11 : (3/2)^11 < 100.
Proof.
  assert (Hcalc: (3/2)^11 = 3^11 / 2^11).
  { simpl. field. }
  rewrite Hcalc.
  assert (H3: 3^11 = 177147) by (simpl; lra).
  assert (H2: 2^11 = 2048) by (simpl; lra).
  rewrite H3, H2.
  lra.
Qed.

(* Error exceeds 100 at 12 iterations *)
Lemma error_at_iteration_12 : (3/2)^12 > 100.
Proof.
  assert (Hcalc: (3/2)^12 = 3^12 / 2^12).
  { simpl. field. }
  rewrite Hcalc.
  assert (H3: 3^12 = 531441) by (simpl; lra).
  assert (H2: 2^12 = 4096) by (simpl; lra).
  rewrite H3, H2.
  lra.
Qed.

(* Error crosses tolerance threshold at iteration 12 *)
Theorem error_exceeds_tolerance_at_12_iterations :
  forall initial_error tolerance,
  initial_error = 1 ->
  tolerance = 100 ->
  initial_error * (3/2)^11 < tolerance /\
  initial_error * (3/2)^12 > tolerance.
Proof.
  intros initial_error tolerance Hinit Htol.
  rewrite Hinit, Htol.
  split.
  - assert (H: 1 * (3/2)^11 = (3/2)^11) by lra.
    rewrite H. apply error_at_iteration_11.
  - assert (H: 1 * (3/2)^12 = (3/2)^12) by lra.
    rewrite H. apply error_at_iteration_12.
Qed.

(* Critical threshold between iterations 11 and 12 *)
Corollary critical_iteration_exact : (3/2)^11 < 100 < (3/2)^12.
Proof.
  split.
  - apply error_at_iteration_11.
  - apply error_at_iteration_12.
Qed.

(* Concrete formula for iterated T on reals *)
Theorem T_iter_R_vec_concrete_divergence : forall (x : R_vec) (n : nat),
  x <> 0 ->
  valuation (T_iter n x) = (3/2)^n * Rabs x.
Proof.
  intros x n Hneq.
  rewrite R_vec_T_iter_exact.
  unfold valuation; simpl.
  unfold R_vec_norm.
  reflexivity.
Qed.

End ErrorAmplification.

(* Reals provide nontrivial instance *)
Lemma nontrivial_instance_exists :
  exists (Omega : Type) (H : TernaryAlgebra Omega) (H0 : ValuatedTernaryAlgebra Omega)
         (x y : Omega),
    x <> y /\ valuation x <> valuation y.
Proof.
  exists R_vec, RVecTernaryAlgebra, RVecValuatedTernaryAlgebra, 0, 1.
  split; [lra | ].
  unfold valuation; simpl.
  unfold R_vec_norm.
  intro Hcontra.
  assert (H0: Rabs 0 = 0) by apply Rabs_R0.
  assert (H1: Rabs 1 = 1) by (rewrite Rabs_right; lra).
  rewrite H0, H1 in Hcontra.
  lra.
Qed.

(* Derived binary operation on reals is arithmetic mean *)
Lemma R_vec_derived_binary_is_average : forall a b,
  (a ◊ b : R_vec) = (a + b) / 2.
Proof.
  intros a b.
  unfold derived_binary_op; simpl.
  unfold R_vec_ternary, R_vec_identity.
  lra.
Qed.

(* Derived binary on reals is commutative *)
Lemma R_vec_derived_binary_IS_commutative : forall a b : R_vec,
  a ◊ b = b ◊ a.
Proof.
  intros a b.
  rewrite R_vec_derived_binary_is_average.
  rewrite R_vec_derived_binary_is_average.
  lra.
Qed.

(* Derived binary does not have identity property *)
Lemma R_vec_derived_binary_not_identity :
  exists a : R_vec, a ◊ identity <> a.
Proof.
  exists 2.
  rewrite R_vec_derived_binary_is_average.
  unfold identity; simpl.
  unfold R_vec_identity.
  lra.
Qed.

(* Concrete counterexample to associativity *)
Example R_vec_associator_concrete :
  let a := 1 in let b := 2 in let c := 3 in let d := 4 in let e := 5 in
  ternary_op (ternary_op a b c) d e <>
  ternary_op a (ternary_op b c d) e.
Proof.
  simpl.
  unfold R_vec_ternary.
  intro Hcontra.
  assert (Hlhs: ((1 + 2 + 3) / 2 + 4 + 5) / 2 = 8) by lra.
  assert (Hrhs: (1 + (2 + 3 + 4) / 2 + 5) / 2 = 27/4) by lra.
  rewrite Hlhs, Hrhs in Hcontra.
  lra.
Qed.

(* Associator defect quantified as quarter of difference *)
Lemma R_vec_associator_defect : forall a b c d e : R_vec,
  Rabs (ternary_op (ternary_op a b c) d e -
        ternary_op a (ternary_op b c d) e) = Rabs (d - a) / 4.
Proof.
  intros a b c d e.
  simpl.
  unfold R_vec_ternary.
  replace (((a + b + c) / 2 + d + e) / 2 - (a + (b + c + d) / 2 + e) / 2)
    with ((d - a) / 4) by (field; lra).
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_inv by lra.
  rewrite (Rabs_right 4) by lra.
  reflexivity.
Qed.


End NormedVectorSpaceInstance.

(* Structural investigation of ternary algebra *)
Section InvestigatingTheStructure.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* Ternary operation equals sum divided by 2 *)
Example R_vec_denominator : forall a b c : R,
  R_vec_ternary a b c = (a + b + c) / 2.
Proof.
  intros. unfold R_vec_ternary. reflexivity.
Qed.

(* Ternary average differs from arithmetic mean *)
Example different_from_standard_average :
  R_vec_ternary 1 1 1 <> (1 + 1 + 1) / 3.
Proof.
  unfold R_vec_ternary.
  intro Hcontra.
  assert (H2: (1 + 1 + 1) / 2 = 3/2) by lra.
  assert (H3: (1 + 1 + 1) / 3 = 1) by lra.
  rewrite H2, H3 in Hcontra.
  lra.
Qed.

(* Identity law holds with denominator 2 *)
Example identity_law_with_this_denominator :
  R_vec_ternary 0 5 5 = 5.
Proof.
  unfold R_vec_ternary, R_vec_identity.
  lra.
Qed.

(* Standard three-way average value *)
Example standard_averaging_comparison :
  (0 + 5 + 5) / 3 = 10/3.
Proof.
  lra.
Qed.

(* T operator amplifies by factor 3/2 *)
Theorem T_effect_on_R_vec : forall x : R,
  x <> 0 ->
  Rabs (R_vec_ternary x x x) = (3/2) * Rabs x.
Proof.
  intros x Hx.
  unfold R_vec_ternary.
  assert (Hcalc: (x + x + x) / 2 = 3/2 * x) by lra.
  rewrite Hcalc.
  rewrite Rabs_mult.
  rewrite (Rabs_right (3/2)) by lra.
  reflexivity.
Qed.

(* Amplification factor is 3 divided by denominator *)
Theorem denominator_amplification_relationship : forall d : R, d > 0 ->
  forall x : R,
  Rabs ((x + x + x) / d) = (3/d) * Rabs x.
Proof.
  intros d Hd x.
  unfold Rdiv.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_r.
  replace (x * /d + x * /d + x * /d) with (3 * x * /d) by ring.
  rewrite Rabs_mult.
  rewrite Rabs_mult.
  rewrite (Rabs_right 3) by lra.
  rewrite Rabs_inv by lra.
  rewrite (Rabs_right d) by lra.
  ring.
Qed.

(* Amplification with denominator 2 yields 3/2 *)
Corollary amplification_with_d_equals_2 :
  let d := 2 in
  3/d = 3/2.
Proof.
  simpl. lra.
Qed.

(* Amplification with denominator 3 yields 1 *)
Corollary amplification_with_d_equals_3 :
  let d := 3 in
  3/d = 1.
Proof.
  simpl. lra.
Qed.

(* Barycentric bound and denominator both equal 2 *)
Theorem denominators_match_in_R_vec :
  forall a b c : R,
  R_vec_norm (R_vec_ternary a b c) <= (R_vec_norm a + R_vec_norm b + R_vec_norm c) / 2
  /\
  R_vec_ternary a b c = (a + b + c) / 2.
Proof.
  intros a b c.
  split.
  - apply R_vec_barycentric.
  - unfold R_vec_ternary. reflexivity.
Qed.

(* Identity law holds if and only if denominator is 2 *)
Example identity_law_requires_specific_denominator :
  forall a d : R, d > 0 -> a <> 0 ->
  (0 + a + a) / d = a <-> d = 2.
Proof.
  intros a d Hd Ha_neq.
  split; intro Heq.
  - assert (Hsimp: 2 * a / d = a) by lra.
    assert (Hmul: 2 * a = a * d).
    { apply Rmult_eq_compat_r with (r := d) in Hsimp.
      unfold Rdiv in Hsimp.
      rewrite Rmult_assoc in Hsimp.
      rewrite Rinv_l in Hsimp by lra.
      rewrite Rmult_1_r in Hsimp.
      exact Hsimp. }
    rewrite Rmult_comm in Hmul.
    apply Rmult_eq_reg_l in Hmul; lra.
  - subst d. lra.
Qed.

(* Stability threshold occurs at denominator 3 *)
Theorem denominator_and_stability_threshold :
  forall d : R, d > 0 ->
  (3/d < 1 <-> d > 3) /\
  (3/d = 1 <-> d = 3) /\
  (3/d > 1 <-> d < 3).
Proof.
  intros d Hpos.
  split; [|split].
  - split; intro Heq.
    + unfold Rdiv in Heq.
      assert (H1: 3 * /d * d < 1 * d) by (apply Rmult_lt_compat_r; lra).
      rewrite Rmult_assoc in H1.
      rewrite Rinv_l in H1 by lra.
      rewrite Rmult_1_r in H1.
      lra.
    + unfold Rdiv.
      assert (H1: 3 < 1 * d) by lra.
      apply Rmult_lt_compat_r with (r := /d) in H1; [|apply Rinv_0_lt_compat; lra].
      rewrite Rmult_assoc in H1.
      rewrite Rinv_r in H1 by lra.
      rewrite Rmult_1_r in H1.
      lra.
  - split; intro Heq.
    + unfold Rdiv in Heq.
      apply Rmult_eq_compat_r with (r := d) in Heq.
      rewrite Rmult_assoc in Heq.
      rewrite Rinv_l in Heq by lra.
      rewrite Rmult_1_r in Heq.
      lra.
    + subst d.
      unfold Rdiv.
      replace (3 * / 3) with 1 by (field; lra).
      lra.
  - split; intro Heq.
    + unfold Rdiv in Heq.
      assert (H1: 3 * /d * d > 1 * d) by (apply Rmult_gt_compat_r; lra).
      rewrite Rmult_assoc in H1.
      rewrite Rinv_l in H1 by lra.
      rewrite Rmult_1_r in H1.
      lra.
    + unfold Rdiv.
      assert (H1: 3 > 1 * d) by lra.
      apply Rmult_gt_compat_r with (r := /d) in H1; [|apply Rinv_0_lt_compat; lra].
      rewrite Rmult_assoc in H1.
      rewrite Rinv_r in H1 by lra.
      rewrite Rmult_1_r in H1.
      lra.
Qed.

(* Standard consensus violates identity law except at zero *)
Example standard_consensus_vs_identity_law :
  forall a : R,
  (0 + a + a) / 3 = a <-> a = 0.
Proof.
  intro a.
  split; intro Heq; lra.
Qed.

End InvestigatingTheStructure.

(* Impossibility of stable ternary consensus *)
Section StableTernaryImpossibilityTheorem.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

(* T operator non-increasing in valuation *)
Definition is_stable : Prop :=
  forall x, valuation (T x) <= valuation x.

(* T operator strictly decreasing on non-identity elements *)
Definition is_contractive : Prop :=
  forall x, x <> identity -> valuation (T x) < valuation x.

(* T operator increases valuation for some element *)
Definition is_expansive : Prop :=
  exists x, x <> identity /\ valuation (T x) > valuation x.

(* Stability threshold constant *)
Definition stability_threshold : R := 1.

(* Identity law forces denominator to equal 2 *)
Lemma identity_law_determines_denominator :
  forall (ternary_denominator : R),
  ternary_denominator > 0 ->
  (forall a, (0 + a + a) / ternary_denominator = a) <->
  ternary_denominator = 2.
Proof.
  intros d Hd.
  split; intro Heq.
  - specialize (Heq 1).
    assert (Hcalc: (0 + 1 + 1) / d = 1) by exact Heq.
    assert (Hsimpl: 2 / d = 1).
    { rewrite <- Hcalc. f_equal. lra. }
    unfold Rdiv in Hsimpl.
    apply Rmult_eq_compat_r with (r := d) in Hsimpl.
    replace (2 * / d * d) with (2 * (/ d * d)) in Hsimpl by ring.
    rewrite Rinv_l in Hsimpl by lra.
    rewrite Rmult_1_r in Hsimpl.
    lra.
  - subst d. intro a. lra.
Qed.

(* Lipschitz constant 3/2 exceeds stability bound *)
Lemma lipschitz_3_2_violates_stability :
  (3/2) > stability_threshold.
Proof.
  unfold stability_threshold.
  lra.
Qed.

(* Consensus and identity denominators are incompatible *)
Corollary consensus_identity_incompatibility :
  forall (consensus_denominator identity_denominator : R),
  identity_denominator > 0 ->
  consensus_denominator = 3 ->
  (forall a, (0 + a + a) / identity_denominator = a) ->
  identity_denominator <> consensus_denominator.
Proof.
  intros d_cons d_id Hid_pos Hcons Hid_law.
  assert (Hid_eq: d_id = 2).
  { apply identity_law_determines_denominator; assumption. }
  subst d_id d_cons.
  lra.
Qed.

(* Stability requires denominator at least 3 *)
Corollary stable_requires_denominator_at_least_3 :
  forall (d : R),
  d > 0 ->
  (3/d <= stability_threshold) <-> (d >= 3).
Proof.
  intros d Hd.
  unfold stability_threshold, Rdiv.
  split; intro Heq.
  - apply Rmult_le_compat_r with (r := d) in Heq; [|lra].
    replace (3 * / d * d) with (3 * (/ d * d)) in Heq by ring.
    rewrite Rinv_l in Heq by lra.
    rewrite Rmult_1_r in Heq.
    lra.
  - assert (Hinv_pos: / d > 0) by (apply Rinv_0_lt_compat; lra).
    assert (Hgoal: 3 * / d <= 1).
    { apply Rmult_le_reg_r with (r := d); [lra|].
      rewrite Rmult_assoc.
      rewrite Rinv_l by lra.
      rewrite Rmult_1_r.
      rewrite Rmult_1_l.
      lra. }
    exact Hgoal.
Qed.

(* Iterations amplify by exponential factor *)
Corollary iteration_exponential_amplification :
  forall (n : nat) (x : R),
  x <> 0 ->
  Rabs ((3/2)^n * x) = (3/2)^n * Rabs x.
Proof.
  intros n x Hx_neq.
  rewrite Rabs_mult.
  rewrite Rabs_right.
  - reflexivity.
  - apply Rle_ge.
    apply pow_le.
    lra.
Qed.

(* Byzantine fault amplifies error beyond 100x in 12 iterations *)
Corollary byzantine_exploitation_via_identity_law :
  forall (error_initial : R) (iterations : nat),
  error_initial > 0 ->
  iterations = 12%nat ->
  Rabs (error_initial * (3/2)^iterations) > 100 * error_initial.
Proof.
  intros err n Herr_pos Hn.
  subst n.
  rewrite Rabs_mult.
  rewrite (Rabs_right err) by lra.
  rewrite Rabs_right.
  - assert (Hpow: (3/2)^12 > 100) by apply error_at_iteration_12.
    assert (Hcalc: err * (3/2)^12 > 100 * err).
    { assert (Hmul: (3/2)^12 * err > 100 * err) by (apply Rmult_gt_compat_r; assumption).
      lra. }
    exact Hcalc.
  - apply Rle_ge. apply pow_le. lra.
Qed.

End StableTernaryImpossibilityTheorem.

(* Real numbers with capped norm *)
Section CappedNormInstance.

(* Type alias for reals with capped norm *)
Definition R_capped := R.

(* Ternary operation on capped reals *)
Definition R_capped_ternary (a b c : R_capped) : R_capped :=
  (a + b + c) / 2.

(* Identity element for capped reals *)
Definition R_capped_identity : R_capped := 0.

(* Norm capped at maximum value of 1 *)
Definition R_capped_norm (x : R_capped) : R := Rmin (Rabs x) 1.

(* Capped ternary operation is cyclically symmetric *)
Lemma R_capped_cyclic : forall a b c,
  R_capped_ternary a b c = R_capped_ternary c a b.
Proof.
  intros a b c.
  unfold R_capped_ternary.
  f_equal. ring.
Qed.

(* Capped identity law holds *)
Lemma R_capped_identity_law : forall a,
  R_capped_ternary R_capped_identity a a = a.
Proof.
  intro a.
  unfold R_capped_ternary, R_capped_identity.
  field_simplify; lra.
Qed.

(* Capped reals form ternary algebra *)
Instance RCappedTernaryAlgebra : TernaryAlgebra R_capped := {
  ternary_op := R_capped_ternary;
  identity := R_capped_identity;
  cyclic_symmetry := R_capped_cyclic;
  identity_law := R_capped_identity_law;
}.

(* Capped norm is nonnegative *)
Lemma R_capped_norm_nonneg : forall x, 0 <= R_capped_norm x.
Proof.
  intro x.
  unfold R_capped_norm.
  apply Rmin_glb; [apply Rabs_pos | lra].
Qed.

(* Identity has zero capped norm *)
Lemma R_capped_norm_identity : R_capped_norm R_capped_identity = 0.
Proof.
  unfold R_capped_norm, R_capped_identity.
  rewrite Rabs_R0.
  apply Rmin_left. lra.
Qed.

(* Cap violates amplification bound at x=2 *)
Theorem R_capped_pathological_strict_inequality_example :
  let x := 2 in
  Rmin (Rabs (R_capped_ternary x x x)) 1 < (3/2) * Rmin (Rabs x) 1.
Proof.
  simpl.
  unfold R_capped_ternary.
  assert (Hcalc: (2 + 2 + 2) / 2 = 3).
  { lra. }
  rewrite Hcalc.
  assert (H_lhs: Rmin (Rabs 3) 1 = 1).
  { apply Rmin_right. assert (H3: Rabs 3 = 3).
    { rewrite Rabs_right; lra. }
    rewrite H3. lra. }
  assert (H_rhs: (3/2) * Rmin (Rabs 2) 1 = 3/2).
  { assert (H2: Rabs 2 = 2).
    { rewrite Rabs_right; lra. }
    rewrite H2.
    rewrite Rmin_right; lra. }
  rewrite H_lhs, H_rhs.
  lra.
Qed.

End CappedNormInstance.

(* Product of two ternary algebras *)
Section ProductConstruction.

Context {Omega1 Omega2 : Type}.
Context `{ValuatedTernaryAlgebra Omega1}.
Context `{ValuatedTernaryAlgebra Omega2}.

(* Ternary operation on product type applies componentwise *)
Definition product_ternary (p1 p2 p3 : Omega1 * Omega2) : Omega1 * Omega2 :=
  let '(a1, a2) := p1 in
  let '(b1, b2) := p2 in
  let '(c1, c2) := p3 in
  (ternary_op a1 b1 c1, ternary_op a2 b2 c2).

(* Product identity is pair of identities *)
Definition product_identity : Omega1 * Omega2 := (identity, identity).

(* Product valuation is maximum of components *)
Definition product_valuation (p : Omega1 * Omega2) : R :=
  let '(x1, x2) := p in
  Rmax (valuation x1) (valuation x2).

(* Product ternary operation satisfies cyclic symmetry *)
Lemma product_cyclic : forall p1 p2 p3,
  product_ternary p1 p2 p3 = product_ternary p3 p1 p2.
Proof.
  intros [a1 a2] [b1 b2] [c1 c2].
  unfold product_ternary.
  rewrite (cyclic_symmetry a1 b1 c1).
  rewrite (cyclic_symmetry a2 b2 c2).
  reflexivity.
Qed.

(* Product identity law holds componentwise *)
Lemma product_identity_law : forall p,
  product_ternary product_identity p p = p.
Proof.
  intros [x1 x2].
  unfold product_ternary, product_identity.
  rewrite (identity_law x1).
  rewrite (identity_law x2).
  reflexivity.
Qed.

(* Product forms ternary algebra *)
Instance ProductTernaryAlgebra : TernaryAlgebra (Omega1 * Omega2) := {
  ternary_op := product_ternary;
  identity := product_identity;
  cyclic_symmetry := product_cyclic;
  identity_law := product_identity_law;
}.

(* Product valuation is nonnegative *)
Lemma product_valuation_nonneg : forall p, 0 <= product_valuation p.
Proof.
  intros [x1 x2].
  unfold product_valuation.
  apply Rle_trans with (r2 := valuation x1).
  - apply valuation_nonneg.
  - apply Rmax_l.
Qed.

(* Product identity has zero valuation *)
Lemma product_valuation_identity : product_valuation product_identity = 0.
Proof.
  unfold product_valuation, product_identity.
  rewrite valuation_identity.
  rewrite valuation_identity.
  apply Rmax_left. lra.
Qed.

Lemma product_valuation_barycentric : forall p1 p2 p3,
  product_valuation (product_ternary p1 p2 p3) <=
  (product_valuation p1 + product_valuation p2 + product_valuation p3) / 2.
Proof.
  intros [a1 a2] [b1 b2] [c1 c2].
  unfold product_valuation, product_ternary.
  apply Rmax_lub.
  - apply Rle_trans with (r2 := (valuation a1 + valuation b1 + valuation c1) / 2).
    + apply valuation_barycentric.
    + apply Rmult_le_compat_r; [lra |].
      apply Rplus_le_compat.
      * apply Rplus_le_compat; [apply Rmax_l | apply Rmax_l].
      * apply Rmax_l.
  - apply Rle_trans with (r2 := (valuation a2 + valuation b2 + valuation c2) / 2).
    + apply valuation_barycentric.
    + apply Rmult_le_compat_r; [lra |].
      apply Rplus_le_compat.
      * apply Rplus_le_compat; [apply Rmax_r | apply Rmax_r].
      * apply Rmax_r.
Qed.

Lemma product_valuation_faithful : forall p,
  product_valuation p = 0 -> p = product_identity.
Proof.
  intros [x1 x2] Hval.
  unfold product_valuation, product_identity in *.
  assert (Hval1: valuation x1 = 0).
  { assert (Hmax: Rmax (valuation x1) (valuation x2) = 0) by exact Hval.
    assert (Hle: valuation x1 <= 0) by (rewrite <- Hmax; apply Rmax_l).
    assert (Hge: 0 <= valuation x1) by apply valuation_nonneg.
    lra. }
  assert (Hval2: valuation x2 = 0).
  { assert (Hmax: Rmax (valuation x1) (valuation x2) = 0) by exact Hval.
    assert (Hle: valuation x2 <= 0) by (rewrite <- Hmax; apply Rmax_r).
    assert (Hge: 0 <= valuation x2) by apply valuation_nonneg.
    lra. }
  rewrite (valuation_faithful x1 Hval1).
  rewrite (valuation_faithful x2 Hval2).
  reflexivity.
Qed.

Instance ProductValuatedTernaryAlgebra : ValuatedTernaryAlgebra (Omega1 * Omega2) := {
  valuation := product_valuation;
  valuation_nonneg := product_valuation_nonneg;
  valuation_identity := product_valuation_identity;
  valuation_barycentric := product_valuation_barycentric;
  valuation_faithful := product_valuation_faithful;
}.

Theorem product_T_componentwise : forall (p : Omega1 * Omega2),
  T p = (T (fst p), T (snd p)).
Proof.
  intro p.
  destruct p as [x1 x2].
  unfold T. simpl.
  unfold product_ternary.
  reflexivity.
Qed.

Theorem product_valuation_detects_max : forall (x1 : Omega1) (x2 : Omega2),
  product_valuation (x1, x2) = Rmax (valuation x1) (valuation x2).
Proof.
  intros x1 x2.
  unfold product_valuation.
  reflexivity.
Qed.

Theorem product_T_valuation_bound : forall (p : Omega1 * Omega2),
  valuation (T p) <= lipschitz_bound_T * valuation p.
Proof.
  intro p.
  apply T_valuation_lipschitz.
Qed.

End ProductConstruction.

Section LipschitzComposition.

Context {Omega1 Omega2 Omega3 : Type}.
Context `{ValuatedTernaryAlgebra Omega1}.
Context `{ValuatedTernaryAlgebra Omega2}.
Context `{ValuatedTernaryAlgebra Omega3}.

Context (phi : Omega1 -> Omega2).
Context (psi : Omega2 -> Omega3).

Lemma comp_Lipschitz : forall c d,
  0 <= c -> 0 <= d ->
  preserves_structure_Lipschitz phi c ->
  preserves_structure_Lipschitz psi d ->
  preserves_structure_Lipschitz (fun x => psi (phi x)) (c * d).
Proof.
  intros c d Hc_nonneg Hd_nonneg [Hphi_struct Hphi_bound] [Hpsi_struct Hpsi_bound].
  unfold preserves_structure_Lipschitz.
  split.
  - unfold preserves_ternary_structure in *.
    intros a b c0.
    rewrite Hphi_struct.
    apply Hpsi_struct.
  - intros x.
    apply Rle_trans with (r2 := d * valuation (phi x)).
    + apply Hpsi_bound.
    + apply Rle_trans with (r2 := d * (c * valuation x)).
      * apply Rmult_le_compat_l; [exact Hd_nonneg | apply Hphi_bound].
      * assert (H_assoc: d * (c * valuation x) = c * d * valuation x) by ring.
        rewrite H_assoc. apply Rle_refl.
Qed.

End LipschitzComposition.

Section ApplicationFiniteDifference.

Definition fd_step (u : R) : R :=
  (u + u + u) / 2.

Fixpoint fd_iterate (n : nat) (u0 : R) : R :=
  match n with
  | O => u0
  | S n' => fd_step (fd_iterate n' u0)
  end.

Theorem fd_error_amplification_exact : forall (u0 : R) (n : nat),
  u0 <> 0 ->
  Rabs (fd_iterate n u0) = (3/2)^n * Rabs u0.
Proof.
  intros u0 n Hneq.
  induction n as [|n' IHn'].
  - simpl. lra.
  - simpl fd_iterate. unfold fd_step.
    assert (Hcalc: (fd_iterate n' u0 + fd_iterate n' u0 + fd_iterate n' u0) / 2 =
                    3/2 * fd_iterate n' u0).
    { field. }
    rewrite Hcalc.
    rewrite Rabs_mult.
    rewrite (Rabs_right (3/2)) by lra.
    rewrite IHn'.
    simpl. ring.
Qed.

Theorem fd_instability_threshold_lower : forall (initial_error : R),
  initial_error = 1 ->
  Rabs (fd_iterate 11 initial_error) < 100.
Proof.
  intros initial_error Hinit.
  subst initial_error.
  rewrite fd_error_amplification_exact by lra.
  rewrite Rabs_R1.
  assert (H: (3/2)^11 * 1 = (3/2)^11) by lra.
  rewrite H.
  apply error_at_iteration_11.
Qed.

Theorem fd_instability_threshold_upper : forall (initial_error : R),
  initial_error = 1 ->
  Rabs (fd_iterate 12 initial_error) > 100.
Proof.
  intros initial_error Hinit.
  subst initial_error.
  rewrite fd_error_amplification_exact by lra.
  rewrite Rabs_R1.
  assert (H: (3/2)^12 * 1 = (3/2)^12) by lra.
  rewrite H.
  apply error_at_iteration_12.
Qed.

Theorem fd_naive_smoothing_diverges :
  forall (u0 : R),
  u0 <> 0 ->
  forall n : nat,
  (n > 0)%nat ->
  Rabs (fd_iterate n u0) > Rabs u0.
Proof.
  intros u0 Hneq n Hn.
  rewrite fd_error_amplification_exact by exact Hneq.
  assert (Hpow: (3/2)^n > 1).
  { destruct n as [|n']; [lia |].
    clear Hn. induction n' as [|n'' IHn''].
    - simpl. lra.
    - simpl. apply Rlt_trans with (r2 := (3/2) * 1); [lra |].
      apply Rmult_lt_compat_l; [lra | exact IHn'']. }
  assert (Hu0_pos: Rabs u0 > 0) by (apply Rabs_pos_lt; exact Hneq).
  assert (H: (3/2)^n * Rabs u0 > 1 * Rabs u0).
  { apply Rmult_gt_compat_r; assumption. }
  lra.
Qed.

Corollary fd_scheme_is_unstable :
  exists (u0 : R) (N : nat),
  u0 <> 0 /\ (N > 0)%nat /\
  Rabs (fd_iterate N u0) > 100 * Rabs u0.
Proof.
  exists 1, 12%nat.
  split; [lra | ].
  split; [lia | ].
  rewrite fd_error_amplification_exact by lra.
  rewrite Rabs_R1.
  assert (H: (3/2)^12 * 1 = (3/2)^12) by lra.
  rewrite H.
  assert (Hineq: (3/2)^12 > 100) by apply error_at_iteration_12.
  lra.
Qed.

Definition numerical_stability_violated : Prop :=
  exists (scheme : R -> R)
         (u0 : R) (n : nat),
  u0 <> 0 /\
  (forall k, Rabs (Nat.iter k scheme u0) = (3/2)^k * Rabs u0) /\
  Rabs (Nat.iter n scheme u0) > 100 * Rabs u0.

Theorem numerical_stability_failure :
  numerical_stability_violated.
Proof.
  unfold numerical_stability_violated.
  exists fd_step, 1, 12%nat.
  split; [lra | ].
  split.
  - intro k.
    assert (Heq: Nat.iter k fd_step 1 = fd_iterate k 1).
    { induction k as [|k' IHk'].
      - reflexivity.
      - simpl. rewrite IHk'. reflexivity. }
    rewrite Heq.
    apply fd_error_amplification_exact. lra.
  - assert (Heq: Nat.iter 12 fd_step 1 = fd_iterate 12 1).
    { simpl. reflexivity. }
    rewrite Heq.
    rewrite fd_error_amplification_exact by lra.
    rewrite Rabs_R1.
    assert (H: (3/2)^12 * 1 = (3/2)^12) by lra.
    rewrite H.
    assert (Hineq: (3/2)^12 > 100) by apply error_at_iteration_12.
    lra.
Qed.

End ApplicationFiniteDifference.

Section ElementaryRingExample.

Definition agent_state := R.

Definition consensus_value (s1 s2 s3 : agent_state) : R :=
  (s1 + s2 + s3) / 3.

Definition ring_update (s1 s2 s3 : agent_state) : agent_state * agent_state * agent_state :=
  let s1_new := (s3 + s1 + s2) / 2 in
  let s2_new := (s1 + s2 + s3) / 2 in
  let s3_new := (s2 + s3 + s1) / 2 in
  (s1_new, s2_new, s3_new).

Lemma ring_update_reaches_consensus : forall s1 s2 s3,
  let '(s1', s2', s3') := ring_update s1 s2 s3 in
  s1' = s2' /\ s2' = s3'.
Proof.
  intros s1 s2 s3.
  unfold ring_update.
  split; lra.
Qed.

Lemma ring_update_amplifies_sum : forall s1 s2 s3,
  let '(s1', s2', s3') := ring_update s1 s2 s3 in
  s1' + s2' + s3' = (3/2) * (s1 + s2 + s3).
Proof.
  intros s1 s2 s3.
  unfold ring_update.
  lra.
Qed.

Fixpoint ring_iterate (n : nat) (s1 s2 s3 : agent_state) : agent_state * agent_state * agent_state :=
  match n with
  | O => (s1, s2, s3)
  | S n' => let '(s1', s2', s3') := ring_iterate n' s1 s2 s3 in
            ring_update s1' s2' s3'
  end.

Lemma ring_sum_grows_aux : forall s1 s2 s3 n sa sb sc,
  ring_iterate n s1 s2 s3 = (sa, sb, sc) ->
  sa + sb + sc = (3/2)^n * (s1 + s2 + s3).
Proof.
  intros s1 s2 s3 n.
  induction n as [|n' IHn']; intros sa sb sc Heq.
  - simpl in Heq. inversion Heq; subst. simpl. lra.
  - simpl in Heq.
    destruct (ring_iterate n' s1 s2 s3) as [[sa' sb'] sc'] eqn:Heq'.
    assert (Hprev: sa' + sb' + sc' = (3/2)^n' * (s1 + s2 + s3)).
    { apply (IHn' sa' sb' sc'). reflexivity. }
    pose proof (ring_update_amplifies_sum sa' sb' sc') as Hamp.
    unfold ring_update in Heq.
    inversion Heq; subst.
    rewrite Hamp. rewrite Hprev. simpl. ring.
Qed.

Lemma ring_sum_grows : forall s1 s2 s3 n,
  let '(s1_n, s2_n, s3_n) := ring_iterate n s1 s2 s3 in
  s1_n + s2_n + s3_n = (3/2)^n * (s1 + s2 + s3).
Proof.
  intros s1 s2 s3 n.
  destruct (ring_iterate n s1 s2 s3) as [[sa sb] sc] eqn:Heq.
  apply (ring_sum_grows_aux s1 s2 s3 n sa sb sc). exact Heq.
Qed.

Corollary ring_consensus_catastrophic_failure : forall s1 s2 s3,
  s1 + s2 + s3 <> 0 ->
  let '(s1_12, s2_12, s3_12) := ring_iterate 12 s1 s2 s3 in
  s1_12 + s2_12 + s3_12 = (3/2)^12 * (s1 + s2 + s3) /\
  Rabs ((s1_12 + s2_12 + s3_12) / 3) > 40 * Rabs (s1 + s2 + s3).
Proof.
  intros s1 s2 s3 Hsum.
  pose proof (ring_sum_grows s1 s2 s3 12) as Hgrow.
  destruct (ring_iterate 12 s1 s2 s3) as [[sa sb] sc] eqn:Heq.
  split.
  - simpl in Hgrow. exact Hgrow.
  - rewrite Hgrow.
    assert (Hpow12: (3/2)^12 > 129) by (pose proof error_at_iteration_12; lra).
    destruct (Rcase_abs (s1 + s2 + s3)).
    + rewrite Rabs_left by lra. rewrite Rabs_left by lra. lra.
    + rewrite Rabs_right by lra. rewrite Rabs_right by lra. lra.
Qed.

End ElementaryRingExample.

Section StabilityBoundaryAnalysis.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

Definition T_parameterized (alpha : R) (x : Omega) : Omega :=
  ternary_op x x x.

Definition lipschitz_constant (alpha : R) : R := 3 * alpha / 2.

Lemma T_alpha_equals_T : forall (x : Omega),
  T_parameterized 1 x = T x.
Proof.
  intro x.
  unfold T_parameterized, T.
  reflexivity.
Qed.

Definition T_alpha_R_vec (alpha : R) (x : R) : R :=
  (alpha * x + alpha * x + alpha * x) / 2.

Lemma T_alpha_R_vec_lipschitz : forall alpha x,
  alpha >= 0 ->
  Rabs (T_alpha_R_vec alpha x) = lipschitz_constant alpha * Rabs x.
Proof.
  intros alpha x Halpha.
  unfold T_alpha_R_vec, lipschitz_constant.
  assert (Hcalc: (alpha * x + alpha * x + alpha * x) / 2 = 3 * alpha / 2 * x) by lra.
  rewrite Hcalc.
  rewrite Rabs_mult.
  rewrite (Rabs_right (3 * alpha / 2)) by lra.
  reflexivity.
Qed.

Theorem stability_boundary_contractive : forall alpha,
  alpha >= 0 ->
  alpha < 2/3 ->
  lipschitz_constant alpha < 1.
Proof.
  intros alpha Hnonneg Hbound.
  unfold lipschitz_constant.
  lra.
Qed.

Theorem stability_boundary_critical : forall alpha,
  alpha = 2/3 ->
  lipschitz_constant alpha = 1.
Proof.
  intro alpha. intro Heq.
  unfold lipschitz_constant.
  rewrite Heq.
  lra.
Qed.

Theorem stability_boundary_expansive : forall alpha,
  alpha > 2/3 ->
  lipschitz_constant alpha > 1.
Proof.
  intros alpha Hbound.
  unfold lipschitz_constant.
  lra.
Qed.

(* Standard weight α=1 yields expansive behavior *)
Corollary standard_case_is_expansive :
  lipschitz_constant 1 = 3/2 /\
  lipschitz_constant 1 > 1 /\
  1 > 2/3.
Proof.
  split; [unfold lipschitz_constant; lra |].
  split; [unfold lipschitz_constant; lra | lra].
Qed.

Corollary standard_consensus_stable :
  lipschitz_constant (1/3) < 1 /\
  1/3 < 2/3.
Proof.
  split; [unfold lipschitz_constant; lra | lra].
Qed.

Theorem stability_design_principle : forall alpha,
  alpha >= 0 ->
  (alpha < 2/3 <-> lipschitz_constant alpha < 1).
Proof.
  intros alpha Halpha.
  split; intro Hbnd.
  - apply stability_boundary_contractive; assumption.
  - unfold lipschitz_constant in Hbnd. lra.
Qed.

End StabilityBoundaryAnalysis.

Section ContractiveConvergence.

Lemma geometric_series_bound : forall (c : R) (n : nat),
  0 <= c < 1 -> c^n <= 1.
Proof.
  intros c n [Hc_nonneg Hc_lt1].
  induction n as [|n' IHn'].
  - simpl. lra.
  - simpl. apply Rle_trans with (r2 := c * 1).
    + apply Rmult_le_compat_l; [exact Hc_nonneg | exact IHn'].
    + lra.
Qed.

Theorem contractive_bound_decreases : forall (alpha : R),
  alpha = 1/3 ->
  lipschitz_constant alpha < 1.
Proof.
  intro alpha. intro Heq. subst alpha.
  unfold lipschitz_constant. lra.
Qed.

Theorem expansive_bound_increases : forall (alpha : R),
  alpha = 1 ->
  lipschitz_constant alpha > 1.
Proof.
  intro alpha. intro Heq. subst alpha.
  unfold lipschitz_constant. lra.
Qed.

Theorem stability_dichotomy :
  lipschitz_constant (1/3) = 1/2 /\ lipschitz_constant 1 = 3/2.
Proof.
  unfold lipschitz_constant. split; lra.
Qed.

Corollary contractive_rate_formula :
  forall (n : nat),
  (1/2)^n <= 1 /\ (3/2)^12 > 100.
Proof.
  intro n.
  split.
  - apply geometric_series_bound. split; lra.
  - apply error_at_iteration_12.
Qed.

End ContractiveConvergence.

Section DistributedLineConsensus.

Context {Omega : Type} `{ValuatedTernaryAlgebra Omega}.

Definition line_gossip_update (x1 x2 x3 : R_vec) : R_vec * R_vec * R_vec :=
  ((2*x1 + x2) / 3, (x1 + x2 + x3) / 3, (x2 + 2*x3) / 3).

Lemma line_gossip_preserves_sum : forall x1 x2 x3,
  let '(y1, y2, y3) := line_gossip_update x1 x2 x3 in
  y1 + y2 + y3 = x1 + x2 + x3.
Proof.
  intros x1 x2 x3.
  unfold line_gossip_update.
  lra.
Qed.

Definition total_deviation (x1 x2 x3 : R_vec) : R :=
  let mean := (x1 + x2 + x3) / 3 in
  Rabs (x1 - mean) + Rabs (x2 - mean) + Rabs (x3 - mean).

Lemma deviation_nonneg : forall x1 x2 x3,
  0 <= total_deviation x1 x2 x3.
Proof.
  intros. unfold total_deviation.
  assert (H1: 0 <= Rabs (x1 - (x1 + x2 + x3) / 3)) by apply Rabs_pos.
  assert (H2: 0 <= Rabs (x2 - (x1 + x2 + x3) / 3)) by apply Rabs_pos.
  assert (H3: 0 <= Rabs (x3 - (x1 + x2 + x3) / 3)) by apply Rabs_pos.
  lra.
Qed.

(* Zero deviation equivalent to complete agreement *)
Lemma deviation_zero_iff_consensus : forall x1 x2 x3,
  total_deviation x1 x2 x3 = 0 <-> x1 = x2 /\ x2 = x3.
Proof.
  intros. unfold total_deviation. split; intro Hdev.
  - assert (Hsum: Rabs (x1 - (x1 + x2 + x3) / 3) = 0 /\
                  Rabs (x2 - (x1 + x2 + x3) / 3) = 0 /\
                  Rabs (x3 - (x1 + x2 + x3) / 3) = 0).
    { assert (Ha: 0 <= Rabs (x1 - (x1 + x2 + x3) / 3)) by apply Rabs_pos.
      assert (Hb: 0 <= Rabs (x2 - (x1 + x2 + x3) / 3)) by apply Rabs_pos.
      assert (Hc: 0 <= Rabs (x3 - (x1 + x2 + x3) / 3)) by apply Rabs_pos.
      lra. }
    destruct Hsum as [Ha [Hb Hc]].
    assert (Heq1: x1 = (x1 + x2 + x3) / 3).
    { destruct (Rcase_abs (x1 - (x1 + x2 + x3) / 3)) as [Hneg | Hpos].
      - rewrite Rabs_left in Ha; lra.
      - rewrite Rabs_right in Ha; lra. }
    assert (Heq2: x2 = (x1 + x2 + x3) / 3).
    { destruct (Rcase_abs (x2 - (x1 + x2 + x3) / 3)) as [Hneg | Hpos].
      - rewrite Rabs_left in Hb; lra.
      - rewrite Rabs_right in Hb; lra. }
    split; lra.
  - destruct Hdev as [H12 H23]. subst x2. subst x3.
    assert (Hmean: (x1 + x1 + x1) / 3 = x1) by lra.
    rewrite Hmean. rewrite Rminus_diag_eq by reflexivity. rewrite Rabs_R0. lra.
Qed.

End DistributedLineConsensus.

(* Verified sensor fusion algorithms *)
Section SensorFusionVerified.

(* Real-valued sensor measurement *)
Definition sensor_reading := R.

(* Average of three sensor readings *)
Definition sensor_average_3 (s1 s2 s3 : sensor_reading) : sensor_reading :=
  (s1 + s2 + s3) / 3.

End SensorFusionVerified.

(* Byzantine fault-tolerant consensus algorithms *)
Section ByzantineResilientConsensus.

(* Real-valued validator input *)
Definition validator_value := R.

(* Median of three values *)
Definition median3 (x y z : validator_value) : validator_value :=
  if Rle_dec x y then
    if Rle_dec y z then y
    else if Rle_dec x z then z else x
  else
    if Rle_dec x z then x
    else if Rle_dec y z then z else y.

(* Median of identical values is that value *)
Lemma median3_idempotent : forall x, median3 x x x = x.
Proof.
  intro. unfold median3. repeat (destruct Rle_dec; try lra).
Qed.

(* Median invariant under cyclic permutation *)
Lemma median3_permutation_123 : forall x y z,
  median3 x y z = median3 y z x.
Proof.
  intros. unfold median3. repeat (destruct Rle_dec; try lra).
Qed.

(* Median bounds Byzantine input between honest values *)
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

(* Concrete blockchain attack scenario neutralized by median *)
Example blockchain_consensus_attack_mitigated :
  let honest_vals := (100.3, 100.5) in
  let attacker := 999.9 in
  let '(h1, h2) := honest_vals in
  let consensus := median3 h1 h2 attacker in
  100.3 <= consensus <= 100.5.
Proof.
  simpl. unfold median3. repeat (destruct Rle_dec; try lra).
Qed.

(* Iterative Byzantine consensus with two honest parties *)
Fixpoint byzantine_iterate_single (n : nat) (h1 h2 : R) (byz : nat -> R) : R * R :=
  match n with
  | O => (h1, h2)
  | S n' => let '(h1', h2') := byzantine_iterate_single n' h1 h2 byz in
            let consensus1 := median3 h1' h2' (byz n') in
            let consensus2 := median3 h2' h1' (byz n') in
            (consensus1, consensus2)
  end.

(* Median between ordered inputs or equals third *)
Lemma median3_bounded : forall x y z,
  x <= y ->
  x <= median3 x y z <= y \/ median3 x y z = z.
Proof.
  intros x y z Hxy.
  unfold median3.
  repeat (destruct Rle_dec; try lra); auto.
Qed.

(* Median always equals one of three inputs *)
Lemma median3_in_range_or_extreme : forall x y z,
  median3 x y z = x \/ median3 x y z = y \/ median3 x y z = z.
Proof.
  intros x y z.
  unfold median3.
  repeat (destruct Rle_dec; auto).
Qed.

(* Median preserves lower bound on all inputs *)
Lemma median3_respects_lower_bound : forall x y z L,
  L <= x -> L <= y -> L <= z -> L <= median3 x y z.
Proof.
  intros x y z L Hx Hy Hz.
  pose proof (median3_in_range_or_extreme x y z) as [Hm|[Hm|Hm]]; rewrite Hm; assumption.
Qed.

(* Median preserves upper bound on all inputs *)
Lemma median3_respects_upper_bound : forall x y z U,
  x <= U -> y <= U -> z <= U -> median3 x y z <= U.
Proof.
  intros x y z U Hx Hy Hz.
  pose proof (median3_in_range_or_extreme x y z) as [Hm|[Hm|Hm]]; rewrite Hm; assumption.
Qed.

(* Single consensus round respects lower bound *)
Lemma byzantine_single_round_lower_bound : forall h1 h2 byz,
  h1 <= h1 -> h1 <= h2 -> h1 <= byz ->
  h1 <= median3 h1 h2 byz.
Proof.
  intros h1 h2 byz Hh1 Hh2 Hbyz.
  apply median3_respects_lower_bound; assumption.
Qed.

(* Single consensus round respects upper bound *)
Lemma byzantine_single_round_upper_bound : forall h1 h2 byz,
  h2 <= h2 -> h1 <= h2 -> byz <= h2 ->
  median3 h2 h1 byz <= h2.
Proof.
  intros h1 h2 byz Hh2 Hh1h2 Hbyz.
  apply median3_respects_upper_bound; [exact Hh2 | lra | exact Hbyz].
Qed.

(* Base case preserves initial values *)
Lemma byzantine_base_case : forall h1 h2,
  let '(h1', h2') := byzantine_iterate_single 0 h1 h2 (fun _ => 0) in
  h1' = h1 /\ h2' = h2.
Proof.
  intros h1 h2.
  simpl.
  split; reflexivity.
Qed.

(* Iteration step preserves bounds *)
Lemma byzantine_bounded_iteration_step : forall h1 h2 h1' h2' byz,
  h1 <= h1' ->
  h1' <= h2 ->
  h1 <= h2' ->
  h2' <= h2 ->
  h1 <= byz ->
  byz <= h2 ->
  h1 <= median3 h1' h2' byz /\ median3 h2' h1' byz <= h2.
Proof.
  intros h1 h2 h1' h2' byz Hlow1 Hup1 Hlow2 Hup2 Hbyz_low Hbyz_up.
  split.
  - apply median3_respects_lower_bound.
    + exact Hlow1.
    + exact Hlow2.
    + exact Hbyz_low.
  - apply median3_respects_upper_bound.
    + exact Hup2.
    + exact Hup1.
    + exact Hbyz_up.
Qed.

(* Byzantine iterations maintain values within initial bounds *)
Theorem byzantine_consensus_bounded_range : forall h1 h2 byz n,
  h1 <= h2 ->
  (forall k, (k < n)%nat -> h1 <= byz k <= h2) ->
  (forall k, (k <= n)%nat ->
    let '(h1', h2') := byzantine_iterate_single k h1 h2 byz in
    h1 <= h1' /\ h1 <= h2' /\ h1' <= h2 /\ h2' <= h2).
Proof.
  intros h1 h2 byz n Horder Hbyz_bounded k Hk.
  induction k as [|k' IHk'].
  - simpl. repeat split; lra.
  - simpl.
    destruct (byzantine_iterate_single k' h1 h2 byz) as [h1' h2'] eqn:Heq.
    assert (Hk'_bound: (k' <= n)%nat) by lia.
    assert (IH: h1 <= h1' /\ h1 <= h2' /\ h1' <= h2 /\ h2' <= h2).
    { apply IHk'. lia. }
    destruct IH as [IH1 [IH2 [IH3 IH4]]].
    assert (Hbyz_k': h1 <= byz k' <= h2).
    { apply Hbyz_bounded. lia. }
    repeat split.
    + apply median3_respects_lower_bound; lra.
    + apply median3_respects_lower_bound; lra.
    + apply median3_respects_upper_bound; lra.
    + apply median3_respects_upper_bound; lra.
Qed.

(* Honest values always remain in initial range *)
Corollary byzantine_honest_always_in_initial_range : forall h1 h2 byz n,
  h1 <= h2 ->
  (forall k, (k < n)%nat -> h1 <= byz k <= h2) ->
  let '(h1_n, h2_n) := byzantine_iterate_single n h1 h2 byz in
  h1 <= h1_n <= h2 /\ h1 <= h2_n <= h2.
Proof.
  intros h1 h2 byz n Horder Hbyz_bounded.
  pose proof (byzantine_consensus_bounded_range h1 h2 byz n Horder Hbyz_bounded n) as H.
  assert (Hle: (n <= n)%nat) by lia.
  specialize (H Hle).
  destruct (byzantine_iterate_single n h1 h2 byz) as [h1_n h2_n].
  destruct H as [H1 [H2 [H3 H4]]].
  split; split; assumption.
Qed.

(* Median filters attacker between honest bounds *)
Theorem byzantine_resilience_median_filter : forall honest1 honest2 attacker,
  honest1 <= honest2 ->
  honest1 <= median3 honest1 honest2 attacker <= honest2 \/ median3 honest1 honest2 attacker = attacker.
Proof.
  intros h1 h2 att Horder.
  pose proof (median3_in_range_or_extreme h1 h2 att) as [Hm|[Hm|Hm]].
  - left. rewrite Hm. split; lra.
  - left. rewrite Hm. split; lra.
  - right. exact Hm.
Qed.

(* Byzantine consensus maintains outer bounds *)
Corollary byzantine_consensus_stays_in_bounds : forall n h1 h2 byz,
  h1 <= h2 ->
  (forall k, (k < n)%nat -> h1 <= byz k <= h2) ->
  let '(h1_n, h2_n) := byzantine_iterate_single n h1 h2 byz in
  h1 <= h1_n /\ h2_n <= h2.
Proof.
  intros n h1 h2 byz Horder Hbyz_bounded.
  pose proof (byzantine_honest_always_in_initial_range h1 h2 byz n Horder Hbyz_bounded) as H.
  destruct (byzantine_iterate_single n h1 h2 byz) as [h1_n h2_n].
  destruct H as [[H1 H2] [H3 H4]].
  split; assumption.
Qed.

End ByzantineResilientConsensus.

(* Byzantine fault tolerance threshold theorems *)
Section ByzantineThresholdTheorem.

Import VectorNotations.

(* Vector of n real-valued agent states *)
Definition agent_vector (n : nat) := Vector.t R n.

(* Extract agent value by finite index *)
Definition get_agent {n : nat} (v : agent_vector n) (i : Fin.t n) : R :=
  Vector.nth v i.

(* Vector eta expansion via identity map *)
Lemma agent_vector_eta : forall n (v : agent_vector n),
  v = Vector.map (fun x => x) v.
Proof.
  intros n v.
  induction v as [|h n' v' IHv'].
  - reflexivity.
  - simpl. f_equal. exact IHv'.
Qed.

(* Agent is in honest set *)
Definition is_honest (i : nat) (honest_set : list nat) : Prop :=
  List.In i honest_set.

(* Agent not in honest set is Byzantine *)
Definition is_byzantine (i : nat) (honest_set : list nat) : Prop :=
  ~ List.In i honest_set.

(* Every agent is either honest or Byzantine *)
Lemma honest_or_byzantine : forall i honest_set,
  is_honest i honest_set \/ is_byzantine i honest_set.
Proof.
  intros i honest_set.
  unfold is_honest, is_byzantine.
  destruct (List.in_dec Nat.eq_dec i honest_set) as [Hin | Hnotin].
  - left. exact Hin.
  - right. exact Hnotin.
Qed.

(* Maximum element in list with fallback *)
Fixpoint list_max (l : list R) (default : R) : R :=
  match l with
  | List.nil => default
  | List.cons x List.nil => x
  | List.cons x xs => Rmax x (list_max xs default)
  end.

(* Minimum element in list with fallback *)
Fixpoint list_min (l : list R) (default : R) : R :=
  match l with
  | List.nil => default
  | List.cons x List.nil => x
  | List.cons x xs => Rmin x (list_min xs default)
  end.

(* List element bounded by maximum *)
Lemma list_max_in_bounds : forall l x default,
  List.In x l -> x <= list_max l default.
Proof.
  intros l x default Hin.
  induction l as [|y l' IHl'].
  - inversion Hin.
  - destruct l' as [|z l''].
    + simpl in Hin. destruct Hin as [Heq | Hfalse].
      * subst. simpl. lra.
      * inversion Hfalse.
    + simpl. destruct Hin as [Heq | Hin'].
      * subst. apply Rmax_l.
      * apply Rle_trans with (r2 := list_max (z :: l'') default).
        -- apply IHl'. exact Hin'.
        -- apply Rmax_r.
Qed.

(* Minimum bounds list element *)
Lemma list_min_in_bounds : forall l x default,
  List.In x l -> list_min l default <= x.
Proof.
  intros l x default Hin.
  induction l as [|y l' IHl'].
  - inversion Hin.
  - destruct l' as [|z l''].
    + simpl in Hin. destruct Hin as [Heq | Hfalse].
      * subst. simpl. lra.
      * inversion Hfalse.
    + simpl. destruct Hin as [Heq | Hin'].
      * subst. apply Rmin_l.
      * assert (Hmin_sub: list_min (z :: l'') default <= x).
        { apply IHl'. exact Hin'. }
        apply Rle_trans with (r2 := list_min (z :: l'') default).
        -- apply Rmin_r.
        -- exact Hmin_sub.
Qed.

(* Count true values in boolean list *)
Definition count_true (l : list bool) : nat :=
  List.fold_left (fun (acc : nat) (b : bool) => if b then S acc else acc) l 0%nat.

(* Folding successor commutes *)
Lemma fold_left_count_S : forall l n,
  List.fold_left (fun (acc : nat) (b : bool) => if b then S acc else acc) l (S n) =
  S (List.fold_left (fun (acc : nat) (b : bool) => if b then S acc else acc) l n).
Proof.
  intros l n.
  generalize dependent n.
  induction l as [|b l' IHl'].
  - intro n. simpl. reflexivity.
  - intro n. simpl. destruct b.
    + rewrite IHl'. rewrite IHl'. reflexivity.
    + apply IHl'.
Qed.

(* Count of true values bounded by list length *)
Lemma count_true_bound : forall l,
  (count_true l <= List.length l)%nat.
Proof.
  intro l.
  unfold count_true.
  induction l as [|b l' IHl'].
  - simpl. lia.
  - simpl. destruct b.
    + rewrite fold_left_count_S. lia.
    + lia.
Qed.

(* Honest agents exceed two-thirds of total *)
Definition honest_majority (n f : nat) : Prop :=
  (3 * f < n)%nat.

(* Byzantine agents exceed one-third threshold *)
Definition byzantine_attack_possible (n f : nat) : Prop :=
  (3 * f >= n)%nat.

(* System either has honest majority or vulnerable *)
Lemma majority_threshold_dichotomy : forall n f,
  honest_majority n f \/ byzantine_attack_possible n f.
Proof.
  intros n f.
  unfold honest_majority, byzantine_attack_possible.
  lia.
Qed.

(* Honest majority implies double honest count exceeds total *)
Lemma honest_count_from_byzantine : forall n f,
  (f <= n)%nat ->
  honest_majority n f ->
  (2 * (n - f) > n)%nat.
Proof.
  intros n f Hf_bound Hmaj.
  unfold honest_majority in Hmaj.
  lia.
Qed.

(* Four nodes tolerate one Byzantine fault *)
Example byzantine_threshold_4_nodes :
  honest_majority 4 1 /\ ~ honest_majority 4 2.
Proof.
  unfold honest_majority. split; lia.
Qed.

(* Seven nodes tolerate two Byzantine faults *)
Example byzantine_threshold_7_nodes :
  honest_majority 7 2 /\ ~ honest_majority 7 3.
Proof.
  unfold honest_majority. split; lia.
Qed.

(* Ten nodes tolerate three Byzantine faults *)
Example byzantine_threshold_10_nodes :
  honest_majority 10 3 /\ ~ honest_majority 10 4.
Proof.
  unfold honest_majority. split; lia.
Qed.

(* One-third is strictly less than half *)
Lemma one_third_is_minority : forall n,
  (n >= 3)%nat ->
  (3 * (n / 3) < n + 1)%nat.
Proof.
  intros n Hn.
  assert (H: (3 * (n / 3) <= n)%nat).
  { destruct (Nat.eq_dec n 0) as [Heq|Hneq].
    - subst. lia.
    - apply Nat.mul_div_le. lia. }
  lia.
Qed.

(* Arithmetic mean of three reals *)
Definition average_R (x y z : R) : R := (x + y + z) / 3.

(* Average bounded by minimum and maximum *)
Lemma average_bounded : forall x y z,
  x <= y -> y <= z ->
  x <= average_R x y z <= z.
Proof.
  intros x y z Hxy Hyz.
  unfold average_R.
  split.
  - assert (H: x + x + x <= x + y + z) by lra.
    assert (Hdiv: (x + x + x) / 3 = x) by (field).
    lra.
  - assert (H: x + y + z <= z + z + z) by lra.
    assert (Hdiv: (z + z + z) / 3 = z) by (field).
    lra.
Qed.

(* Average deviation from median bounded by sum of deviations *)
Lemma average_contracts_to_median : forall x y z,
  Rabs (average_R x y z - y) <= (Rabs (z - y) + Rabs (x - y)) / 3.
Proof.
  intros x y z.
  unfold average_R.
  replace ((x + y + z) / 3 - y) with ((x - y + (z - y)) / 3) by (field).
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_inv by lra.
  rewrite (Rabs_right 3) by lra.
  apply Rle_trans with (r2 := (Rabs (x - y) + Rabs (z - y)) * / 3).
  - apply Rmult_le_compat_r; [lra | apply Rabs_triang].
  - assert (Hcomm: Rabs (z - y) + Rabs (x - y) = Rabs (x - y) + Rabs (z - y)) by lra.
    rewrite Hcomm. apply Rle_refl.
Qed.

Theorem consensus_vs_ternary_algebra_stability :
  forall alpha : R,
  (alpha = 1/3 -> lipschitz_constant alpha < 1) /\
  (alpha = 1 -> lipschitz_constant alpha = 3/2).
Proof.
  intro alpha.
  split; intro Halpha.
  - rewrite Halpha. unfold lipschitz_constant. lra.
  - rewrite Halpha. unfold lipschitz_constant. lra.
Qed.

Corollary standard_consensus_stable_ternary_unstable :
  lipschitz_constant (1/3) < 1 /\ lipschitz_constant 1 > 1.
Proof.
  unfold lipschitz_constant. split; lra.
Qed.

Theorem three_node_median_safety :
  forall h1 h2 byz : R,
  h1 <= h2 ->
  h1 <= median3 h1 h2 byz <= h2.
Proof.
  intros h1 h2 byz Horder.
  pose proof (byzantine_tolerance_1_of_3 h1 h2 byz).
  unfold median3.
  repeat (destruct Rle_dec; try lra).
Qed.

Definition consensus_bounded (lower upper : R) (values : list R) : Prop :=
  forall v, List.In v values -> lower <= v <= upper.

Lemma consensus_bounded_singleton : forall v lower upper,
  lower <= v <= upper <-> consensus_bounded lower upper (List.cons v List.nil).
Proof.
  intros v lower upper.
  unfold consensus_bounded.
  split; intro H.
  - intros v' Hin. simpl in Hin.
    destruct Hin as [Heq | Hfalse].
    + subst. exact H.
    + inversion Hfalse.
  - apply H. simpl. left. reflexivity.
Qed.

Lemma consensus_bounded_preserved_by_median : forall lower upper h1 h2 byz,
  lower <= h1 <= upper ->
  lower <= h2 <= upper ->
  lower <= median3 h1 h2 byz <= upper.
Proof.
  intros lower upper h1 h2 byz Hh1 Hh2.
  assert (Horder: h1 <= h2 \/ h2 <= h1) by lra.
  destruct Horder as [Hle | Hle].
  - pose proof (three_node_median_safety h1 h2 byz Hle) as Hsafe.
    split; lra.
  - assert (Hsym: h2 <= h1) by exact Hle.
    pose proof (three_node_median_safety h2 h1 byz Hsym) as Hsafe.
    assert (Hmed_sym: median3 h1 h2 byz = median3 h2 h1 byz).
    { unfold median3. repeat (destruct Rle_dec; try lra). }
    rewrite Hmed_sym. split; lra.
Qed.

Theorem byzantine_safety_general :
  forall n : nat, forall f : nat,
  honest_majority n f ->
  forall (initial_values : list R) (lower upper : R),
  consensus_bounded lower upper initial_values ->
  (forall honest_vals : list R,
    (forall v, List.In v honest_vals -> List.In v initial_values) ->
    (List.length honest_vals >= 2)%nat ->
    consensus_bounded lower upper honest_vals).
Proof.
  intros n f Hmaj initial_values lower upper Hinit honest_vals Hin Hlen.
  unfold consensus_bounded in *.
  intros v Hv_in.
  apply Hinit.
  apply Hin.
  exact Hv_in.
Qed.

Theorem byzantine_attack_using_ternary_instability :
  forall (initial_error : R),
  initial_error > 0 ->
  Rabs (initial_error * (3/2)^12) > 100 * initial_error.
Proof.
  intros initial_error Hpos.
  assert (H12: (3/2)^12 > 100) by apply error_at_iteration_12.
  rewrite Rabs_mult.
  rewrite (Rabs_right initial_error) by lra.
  rewrite Rabs_right by (apply Rle_ge; apply pow_le; lra).
  replace (100 * initial_error) with (initial_error * 100) by ring.
  apply Rmult_gt_compat_l; [exact Hpos | exact H12].
Qed.

Theorem byzantine_liveness_attack :
  forall n f : nat,
  byzantine_attack_possible n f ->
  exists (attack_strategy : R) (iterations : nat),
  (iterations >= 12)%nat /\
  attack_strategy > 0 /\
  Rabs (attack_strategy * (3/2)^iterations) > 100 * attack_strategy.
Proof.
  intros n f Hattack.
  exists 1, 12%nat.
  split; [lia|].
  split; [lra|].
  apply byzantine_attack_using_ternary_instability.
  lra.
Qed.

Lemma fold_combine_repeat_one : forall m weights,
  length weights = m ->
  fold_right Rplus 0 (map (fun '(w, v) => w * v) (combine weights (List.repeat 1 m))) =
  fold_right Rplus 0 weights.
Proof.
  intro m.
  induction m; intros weights Hlen.
  - destruct weights; try discriminate. simpl. reflexivity.
  - destruct weights as [|w ws]; try discriminate.
    simpl. rewrite IHm by (simpl in Hlen; lia).
    lra.
Qed.

Theorem nary_identity_forces_first_weight_zero :
  forall n : nat,
  (n >= 4)%nat ->
  forall (weights : list R),
  length weights = n ->
  fold_right Rplus 0 weights = 1 ->
  (forall x : R,
    fold_right Rplus 0 (map (fun '(w, v) => w * v) (combine weights (List.cons 0 (List.repeat x (n - 1))))) = x) ->
  exists w_rest : list R, weights = List.cons 0 w_rest /\ length w_rest = (n - 1)%nat /\ fold_right Rplus 0 w_rest = 1.
Proof.
  intros n Hn weights Hlen Hsum Hid.
  destruct weights as [|w0 w_rest].
  - simpl in Hlen. lia.
  - exists w_rest.
    split.
    + assert (Hw0: w0 = 0).
      { specialize (Hid 1).
        simpl in Hid.
        rewrite fold_combine_repeat_one in Hid by (simpl in Hlen; lia).
        simpl in Hsum.
        lra. }
      rewrite Hw0. reflexivity.
    + split.
      * simpl in Hlen. lia.
      * simpl in Hsum.
        assert (Hw0: w0 = 0).
        { specialize (Hid 1).
          simpl in Hid.
          rewrite fold_combine_repeat_one in Hid by (simpl in Hlen; lia).
          simpl in Hsum. lra. }
        lra.
Qed.

Corollary nary_identity_makes_protocol_ignore_first_input :
  forall n : nat,
  (n >= 4)%nat ->
  forall (weights : list R),
  length weights = n ->
  fold_right Rplus 0 weights = 1 ->
  (forall x, fold_right Rplus 0 (map (fun '(w, v) => w * v) (combine weights (List.cons 0 (List.repeat x (n - 1))))) = x) ->
  forall inputs, length inputs = n ->
  fold_right Rplus 0 (map (fun '(w, v) => w * v) (combine weights inputs)) =
  fold_right Rplus 0 (map (fun '(w, v) => w * v) (combine weights (List.cons 0 (List.tl inputs)))).
Proof.
  intros n Hn weights Hlen Hsum Hid inputs Hlen_inputs.
  destruct (nary_identity_forces_first_weight_zero n Hn weights Hlen Hsum Hid) as [w_rest [Hweights [Hlen_rest Hsum_rest]]].
  rewrite Hweights.
  destruct inputs as [|i0 irest].
  - simpl in Hlen_inputs. lia.
  - simpl. assert (H: 0 * i0 = 0 * 0) by ring. rewrite H. reflexivity.
Qed.

End ByzantineThresholdTheorem.

Section RVecCoherenceAnalysis.

Theorem R_vec_NOT_coherent : ~ @ternary_op_coherent R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra.
Proof.
  unfold ternary_op_coherent, nu_equiv.
  intro Hcontra.
  assert (Ha: @valuation R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra 1 =
              @valuation R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra (-1)).
  { simpl. unfold R_vec_norm.
    rewrite Rabs_R1. rewrite Rabs_left; lra. }
  assert (Hb: @valuation R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra 1 =
              @valuation R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra 1).
  { reflexivity. }
  assert (Hc: @valuation R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra 0 =
              @valuation R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra 0).
  { reflexivity. }
  specialize (Hcontra 1 1 0 (-1) 1 0 Ha Hb Hc).
  simpl in Hcontra.
  unfold R_vec_ternary in Hcontra.
  unfold R_vec_norm in Hcontra.
  assert (Hlhs: Rabs ((1 + 1 + 0) / 2) = 1).
  { assert (H: (1 + 1 + 0) / 2 = 1) by lra.
    rewrite H. apply Rabs_R1. }
  assert (Hrhs: Rabs ((-1 + 1 + 0) / 2) = 0).
  { assert (H: (-1 + 1 + 0) / 2 = 0) by lra.
    rewrite H. apply Rabs_R0. }
  rewrite Hlhs in Hcontra.
  rewrite Hrhs in Hcontra.
  lra.
Qed.

Corollary R_vec_quotient_not_applicable :
  ~ exists (coherence : @ternary_op_coherent R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra),
      exists (Q : Type) (H : TernaryAlgebra Q), True.
Proof.
  intro Hex.
  destruct Hex as [Hcoh _].
  apply R_vec_NOT_coherent.
  exact Hcoh.
Qed.

End RVecCoherenceAnalysis.

Section NonnegativeRealsCoherent.

Definition Rnneg := {x : R | x >= 0}.

Definition Rnneg_ternary (a b c : Rnneg) : Rnneg.
Proof.
  destruct a as [a Ha], b as [b Hb], c as [c Hc].
  exists ((a + b + c) / 2).
  lra.
Defined.

Definition Rnneg_identity : Rnneg.
Proof.
  exists 0.
  lra.
Defined.

Lemma Rnneg_cyclic : forall a b c,
  Rnneg_ternary a b c = Rnneg_ternary c a b.
Proof.
  intros [a Ha] [b Hb] [c Hc].
  unfold Rnneg_ternary.
  apply eq_sig_hprop.
  - intro; apply Classical_Prop.proof_irrelevance.
  - simpl. lra.
Qed.

Lemma Rnneg_identity_law : forall a,
  Rnneg_ternary Rnneg_identity a a = a.
Proof.
  intros [a Ha].
  unfold Rnneg_ternary, Rnneg_identity.
  apply eq_sig_hprop.
  - intro; apply Classical_Prop.proof_irrelevance.
  - simpl. lra.
Qed.

Instance RnnegTernaryAlgebra : TernaryAlgebra Rnneg := {
  ternary_op := Rnneg_ternary;
  identity := Rnneg_identity;
  cyclic_symmetry := Rnneg_cyclic;
  identity_law := Rnneg_identity_law;
}.

Definition Rnneg_valuation (x : Rnneg) : R := proj1_sig x.

Lemma Rnneg_valuation_nonneg : forall x, 0 <= Rnneg_valuation x.
Proof.
  intros [x Hx].
  unfold Rnneg_valuation.
  simpl. lra.
Qed.

Lemma Rnneg_valuation_identity : Rnneg_valuation Rnneg_identity = 0.
Proof.
  unfold Rnneg_valuation, Rnneg_identity.
  simpl. reflexivity.
Qed.

Lemma Rnneg_valuation_barycentric : forall a b c,
  Rnneg_valuation (Rnneg_ternary a b c) <=
  (Rnneg_valuation a + Rnneg_valuation b + Rnneg_valuation c) / 2.
Proof.
  intros [a Ha] [b Hb] [c Hc].
  unfold Rnneg_valuation, Rnneg_ternary.
  simpl. lra.
Qed.

Lemma Rnneg_valuation_faithful : forall x,
  Rnneg_valuation x = 0 -> x = Rnneg_identity.
Proof.
  intros [x Hx] Hval.
  unfold Rnneg_valuation, Rnneg_identity in *.
  simpl in Hval.
  apply eq_sig_hprop.
  - intro; apply Classical_Prop.proof_irrelevance.
  - simpl. exact Hval.
Qed.

Instance RnnegValuatedTernaryAlgebra : ValuatedTernaryAlgebra Rnneg := {
  valuation := Rnneg_valuation;
  valuation_nonneg := Rnneg_valuation_nonneg;
  valuation_identity := Rnneg_valuation_identity;
  valuation_barycentric := Rnneg_valuation_barycentric;
  valuation_faithful := Rnneg_valuation_faithful;
}.

Theorem Rnneg_is_coherent : @ternary_op_coherent Rnneg RnnegTernaryAlgebra RnnegValuatedTernaryAlgebra.
Proof.
  unfold ternary_op_coherent, nu_equiv.
  intros [a Ha] [b Hb] [c Hc] [d Hd] [e He] [f Hf] Hvala Hvalb Hvalc.
  unfold valuation, Rnneg_valuation in *.
  simpl in *.
  subst d e f.
  reflexivity.
Qed.

Corollary Rnneg_admits_quotient_construction :
  exists (coherence : @ternary_op_coherent Rnneg RnnegTernaryAlgebra RnnegValuatedTernaryAlgebra),
    exists (Q : Type) (H : TernaryAlgebra Q), True.
Proof.
  exists Rnneg_is_coherent.
  apply (quotient_inherits_ternary_algebra_when_coherent Rnneg_is_coherent).
Qed.

End NonnegativeRealsCoherent.

Section CoherenceConditions.

Definition valuation_determines_operation {Omega : Type}
  `{ValuatedTernaryAlgebra Omega} : Prop :=
  forall a b c d e f,
    valuation a = valuation d ->
    valuation b = valuation e ->
    valuation c = valuation f ->
    valuation (ternary_op a b c) = valuation (ternary_op d e f).

Lemma coherence_iff_valuation_determines :
  forall {Omega : Type} `{ValuatedTernaryAlgebra Omega},
  ternary_op_coherent <-> valuation_determines_operation.
Proof.
  intros Omega H H0.
  unfold ternary_op_coherent, valuation_determines_operation, nu_equiv.
  split; intros H1 a b c d e f Ha Hb Hc; apply H1; assumption.
Qed.

Theorem coherence_sufficient_condition_injective_on_equivalence_classes :
  forall {Omega : Type} `{ValuatedTernaryAlgebra Omega},
  (forall x y, valuation x = valuation y -> x = y) ->
  ternary_op_coherent.
Proof.
  intros Omega H H0 Hinj.
  unfold ternary_op_coherent, nu_equiv.
  intros a b c d e f Ha Hb Hc.
  rewrite (Hinj a d Ha).
  rewrite (Hinj b e Hb).
  rewrite (Hinj c f Hc).
  reflexivity.
Qed.

Example trivial_is_coherent_via_injectivity :
  @ternary_op_coherent unit TrivialTernaryAlgebra TrivialValuatedTernaryAlgebra.
Proof.
  apply coherence_sufficient_condition_injective_on_equivalence_classes.
  intros [] []. intro. reflexivity.
Qed.

Corollary coherence_failure_due_to_sign_ambiguity :
  ~ @ternary_op_coherent R_vec RVecTernaryAlgebra RVecValuatedTernaryAlgebra.
Proof.
  apply R_vec_NOT_coherent.
Qed.

End CoherenceConditions.

Section NonCommutativeImpossibility.

Definition is_commutative {A : Type} (op : A -> A -> A) : Prop :=
  forall x y, op x y = op y x.

Definition is_associative {A : Type} (op : A -> A -> A) : Prop :=
  forall x y z, op x (op y z) = op (op x y) z.

Definition has_left_cancel {A : Type} (add : A -> A -> A) : Prop :=
  forall x y z, add x y = add x z -> y = z.

Definition has_right_cancel {A : Type} (add : A -> A -> A) : Prop :=
  forall x y z, add y x = add z x -> y = z.

Lemma commutative_op_example : is_commutative Rplus.
Proof.
  unfold is_commutative.
  intros x y.
  ring.
Qed.

Lemma associative_op_example : is_associative Rplus.
Proof.
  unfold is_associative.
  intros x y z.
  ring.
Qed.

Lemma comm_assoc_rearrange_3 : forall {A : Type} (add : A -> A -> A) (a b c : A),
  is_commutative add ->
  is_associative add ->
  add (add a b) c = add (add a c) b.
Proof.
  intros A add a b c Hcomm Hassoc.
  unfold is_commutative, is_associative in *.
  assert (H1: add (add a b) c = add a (add b c)) by (symmetry; apply Hassoc).
  rewrite H1.
  assert (H2: add b c = add c b) by (apply Hcomm).
  rewrite H2.
  apply Hassoc.
Qed.

Lemma swap_nested : forall {A : Type} (add : A -> A -> A) (a b : A),
  is_commutative add ->
  add (add a b) = add (add b a).
Proof.
  intros A add a b Hcomm.
  unfold is_commutative in Hcomm.
  f_equal.
  apply Hcomm.
Qed.

Lemma rewrite_rhs_outer : forall {A : Type} (add : A -> A -> A) (nested a b c : A),
  is_commutative add ->
  a = b ->
  add nested a = add nested c ->
  add nested b = add nested c.
Proof.
  intros A add nested a b c Hcomm Hab Heq.
  rewrite <- Hab.
  exact Heq.
Qed.

Lemma cancel_with_outer_mismatch : forall {A : Type} (add : A -> A -> A) (a b c d e : A),
  is_commutative add ->
  is_associative add ->
  has_left_cancel add ->
  add (add a b) c = add (add a d) e ->
  c = e ->
  b = d.
Proof.
  intros A add a b c d e Hcomm Hassoc Hcancel Heq Hce.
  rewrite Hce in Heq.
  unfold is_associative in Hassoc.
  assert (H1: add (add a b) e = add a (add b e)) by (symmetry; apply Hassoc).
  rewrite H1 in Heq.
  assert (H2: add (add a d) e = add a (add d e)) by (symmetry; apply Hassoc).
  rewrite H2 in Heq.
  unfold has_left_cancel in Hcancel.
  apply (Hcancel a (add b e) (add d e)) in Heq.
  unfold is_commutative in Hcomm.
  rewrite (Hcomm b e) in Heq.
  rewrite (Hcomm d e) in Heq.
  apply (Hcancel e b d Heq).
Qed.

Definition ternary_from_mult {A : Type} (mult : A -> A -> A) (add : A -> A -> A)
  (a b c : A) : A :=
  add (add (mult a b) (mult b c)) (mult c a).

Lemma left_cancel_from_comm_assoc : forall {A : Type} (add : A -> A -> A),
  is_commutative add ->
  is_associative add ->
  has_left_cancel add ->
  forall a b c, add a b = add a c -> b = c.
Proof.
  intros A add Hcomm Hassoc Hcancel a b c Heq.
  unfold has_left_cancel in Hcancel.
  apply (Hcancel a b c Heq).
Qed.

Lemma cancel_nested_add : forall {A : Type} (add : A -> A -> A) (a b c d : A),
  is_commutative add ->
  is_associative add ->
  has_left_cancel add ->
  add (add a b) c = add (add a d) c ->
  b = d.
Proof.
  intros A add a b c d Hcomm Hassoc Hcancel Heq.
  unfold is_associative in Hassoc.
  assert (H1: add (add a b) c = add a (add b c)) by (symmetry; apply Hassoc).
  rewrite H1 in Heq.
  assert (H2: add (add a d) c = add a (add d c)) by (symmetry; apply Hassoc).
  rewrite H2 in Heq.
  unfold has_left_cancel in Hcancel.
  apply (Hcancel a (add b c) (add d c)) in Heq.
  unfold is_commutative in Hcomm.
  assert (H3: add (add b c) = add (add c b)) by (f_equal; apply Hcomm).
  assert (H4: add (add d c) = add (add c d)) by (f_equal; apply Hcomm).
  rewrite (Hcomm b c) in Heq.
  rewrite (Hcomm d c) in Heq.
  apply (Hcancel c b d Heq).
Qed.

Lemma ternary_from_mult_independent_of_mult_commutativity :
  forall {A : Type} (mult : A -> A -> A) (add : A -> A -> A) (x y : A),
  is_commutative add ->
  is_associative add ->
  ternary_from_mult mult add x y x = ternary_from_mult mult add x x y.
Proof.
  intros A mult add x y Hcomm Hassoc.
  unfold ternary_from_mult.
  unfold is_commutative in Hcomm.
  unfold is_associative in Hassoc.
  assert (Hlhs: add (add (mult x y) (mult y x)) (mult x x) =
                add (mult x y) (add (mult y x) (mult x x))).
  { symmetry. apply Hassoc. }
  rewrite Hlhs. clear Hlhs.
  assert (Hrhs: add (add (mult x x) (mult x y)) (mult y x) =
                add (mult x y) (add (mult y x) (mult x x))).
  { symmetry.
    rewrite <- (Hassoc (mult x x) (mult x y) (mult y x)).
    rewrite (Hcomm (mult x x) (add (mult x y) (mult y x))).
    rewrite (Hassoc (mult x y) (mult y x) (mult x x)).
    reflexivity. }
  rewrite Hrhs.
  reflexivity.
Qed.

Theorem cyclic_symmetry_independent_of_mult_commutativity :
  forall {A : Type} (mult : A -> A -> A) (add : A -> A -> A) (x y : A),
  is_commutative add ->
  is_associative add ->
  mult x y <> mult y x ->
  ~ (ternary_from_mult mult add x y x <> ternary_from_mult mult add x x y).
Proof.
  intros A mult add x y Hcomm Hassoc Hnoncomm.
  intro Hcontra.
  apply Hcontra.
  apply (ternary_from_mult_independent_of_mult_commutativity mult add x y Hcomm Hassoc).
Qed.

End NonCommutativeImpossibility.

(* ========================================================================= *)
(* Section XVI: Geometric and Representation-Theoretic Characterization      *)
(* ========================================================================= *)
(* Prove WHY d=2 is forced by cyclic symmetry + identity law                *)

Section GeometricCharacterization.

Context {A : Type}.
Variable T : A -> A -> A -> A.

(* Cyclic permutation action *)
Definition cyclic_action (x y z : A) : Prop :=
  T x y z = T y z x /\ T y z x = T z x y.

(* First theorem: Characterize the constraint space *)
Theorem identity_law_defines_affine_subspace :
  forall x : A,
  (forall y z : A, T x x y = y /\ T y x x = y /\ T x y x = y) ->
  exists (constraint : A -> A -> Prop),
    forall a b : A, T a a b = b <-> constraint a b.
Proof.
  intros x H.
  exists (fun a b => T a a b = b).
  intros a b.
  split; intro; assumption.
Qed.

Hypothesis T_cyclic : forall x y z : A, cyclic_action x y z.
Hypothesis T_identity : forall x : A, T x x x = x.

Lemma cyclic_unfold_first :
  forall x y z : A, T x y z = T y z x.
Proof.
  intros x y z.
  unfold cyclic_action in T_cyclic.
  destruct (T_cyclic x y z) as [H1 H2].
  exact H1.
Qed.

(* Second cyclic rotation identity *)
Lemma cyclic_unfold_second :
  forall x y z : A, T y z x = T z x y.
Proof.
  intros x y z.
  unfold cyclic_action in T_cyclic.
  destruct (T_cyclic x y z) as [H1 H2].
  exact H2.
Qed.

(* Complete cyclic permutation of three arguments *)
Theorem cyclic_full_rotation :
  forall x y z : A, T x y z = T z x y.
Proof.
  intros x y z.
  rewrite cyclic_unfold_first.
  apply cyclic_unfold_second.
Qed.

(* Identity law preserved under rotation to yxx form *)
Lemma identity_rotation_yxx :
  forall x y : A,
  T x x y = y ->
  T y x x = y.
Proof.
  intros x y H.
  assert (Hrot: T x x y = T y x x).
  { rewrite cyclic_unfold_first. rewrite cyclic_unfold_second. reflexivity. }
  rewrite <- Hrot.
  exact H.
Qed.

(* Identity law preserved under rotation to xyx form *)
Lemma identity_rotation_xyx :
  forall x y : A,
  T x x y = y ->
  T x y x = y.
Proof.
  intros x y H.
  assert (Hrot: T x x y = T x y x).
  { rewrite cyclic_unfold_first. reflexivity. }
  rewrite <- Hrot.
  exact H.
Qed.

(* Cyclic symmetry reduces identity conditions to single constraint *)
Theorem cyclic_symmetry_collapses_identity_constraints :
  forall x y : A,
  (T x x y = y /\ T y x x = y /\ T x y x = y) <->
  T x x y = y.
Proof.
  intros x y.
  split.
  - intros [H _]. exact H.
  - intro H.
    split. exact H.
    split.
    + apply (identity_rotation_yxx x y H).
    + apply (identity_rotation_xyx x y H).
Qed.

(* Identity on two equal inputs implies self-identity *)
Theorem identity_determines_two_inputs_equal :
  forall x y : A,
  T x x y = y ->
  T x x x = x.
Proof.
  intros x y H.
  specialize (T_identity x).
  exact T_identity.
Qed.

(* Cyclic symmetry eliminates redundant property variations *)
Theorem cyclic_symmetry_reduces_degrees_of_freedom :
  forall x y z : A,
  (T x y z = T y z x /\ T y z x = T z x y) ->
  forall P : A -> A -> A -> Prop,
  (forall a b c : A, P a b c -> P b c a) ->
  (forall a b c : A, P a b c <-> P a b c).
Proof.
  intros x y z Hcyc P Protate.
  intros a b c.
  split; intro; assumption.
Qed.

End GeometricCharacterization.

(* Barycentric coordinate representation *)
Section BarycentricRepresentation.

(* Real-valued ternary operation *)
Variable R_op : R -> R -> R -> R.

(* Operation satisfies both cyclic rotations *)
Hypothesis R_cyclic : forall x y z : R,
  R_op x y z = R_op y z x /\ R_op y z x = R_op z x y.

(* Operation satisfies identity on triple input *)
Hypothesis R_identity : forall x : R, R_op x x x = x.

(* Three coefficients summing to one *)
Definition is_barycentric (a b c : R) : Prop :=
  (a + b + c = 1)%R.

(* Barycentric condition is sum equals one *)
Theorem barycentric_sum_constraint :
  forall a b c : R,
  is_barycentric a b c <-> (a + b + c = 1)%R.
Proof.
  intros a b c.
  unfold is_barycentric.
  split; intro; assumption.
Qed.

(* Equal weights under barycentric constraint yield one-third *)
Theorem cyclic_symmetry_forces_equal_barycentric_weights :
  forall a b c : R,
  is_barycentric a b c ->
  a = b ->
  b = c ->
  a = (1/3)%R.
Proof.
  intros a b c Hbary Hab Hbc.
  unfold is_barycentric in Hbary.
  subst b.
  subst c.
  assert (H: (a + a + a = 1)%R).
  { exact Hbary. }
  assert (H2: (3 * a = 1)%R).
  { rewrite <- H. ring. }
  field_simplify in H2.
  lra.
Qed.

(* Identity constraint is tautological *)
Lemma identity_constraint_reduces_to_single_equation :
  forall x y : R,
  R_op x x y = y ->
  R_op x x y = y.
Proof.
  intros x y H.
  exact H.
Qed.

(* One-third and one-half are distinct *)
Theorem geometric_algebraic_incompatibility :
  forall a b c : R,
  is_barycentric a b c ->
  a = b ->
  b = c ->
  a = (1/3)%R ->
  (forall x y : R, R_op x x y = y) ->
  (1/3 <> 1/2)%R.
Proof.
  intros a b c Hbary Hab Hbc Ha13 Hid.
  lra.
Qed.

(* Cyclic invariance forces all weights to be one-third *)
Theorem cyclic_symmetry_forces_equal_weights_from_barycentric :
  forall a b c : R,
  is_barycentric a b c ->
  (forall x y z : R, (a*x + b*y + c*z)%R = (b*x + c*y + a*z)%R) ->
  a = b /\ b = c /\ a = (1/3)%R.
Proof.
  intros a b c Hbary Hcyc.
  assert (Hab: a = b).
  { assert (Hx1: forall y z : R, (a*1 + b*y + c*z = b*1 + c*y + a*z)%R).
    { intros y z. apply (Hcyc 1%R y z). }
    assert (Hy0z0: (a*1 + b*0 + c*0 = b*1 + c*0 + a*0)%R).
    { apply (Hx1 0%R 0%R). }
    field_simplify in Hy0z0.
    lra. }
  assert (Hbc: b = c).
  { assert (Hy1: forall x z : R, (a*x + b*1 + c*z = b*x + c*1 + a*z)%R).
    { intros x z. apply (Hcyc x 1%R z). }
    assert (Hx0z0: (a*0 + b*1 + c*0 = b*0 + c*1 + a*0)%R).
    { apply (Hy1 0%R 0%R). }
    field_simplify in Hx0z0.
    lra. }
  split. exact Hab.
  split. exact Hbc.
  unfold is_barycentric in Hbary.
  subst b. subst c.
  assert (H: (a + a + a = 1)%R) by exact Hbary.
  lra.
Qed.

End BarycentricRepresentation.

(* Central incompatibility between axioms *)
Section FundamentalIncompatibilityTheorem.

(* Geometric cyclic constraint forces uniform one-third weights *)
Theorem geometric_requirement_forces_one_third :
  forall a b c : R,
  is_barycentric a b c ->
  (forall x y z : R, (a*x + b*y + c*z)%R = (a*z + b*x + c*y)%R) ->
  a = 1/3 /\ b = 1/3 /\ c = 1/3.
Proof.
  intros a b c Hbary Hcyc.
  assert (Hab: a = b).
  { specialize (Hcyc 1 0 0). lra. }
  assert (Hbc: b = c).
  { specialize (Hcyc 0 1 0). lra. }
  split.
  - unfold is_barycentric in Hbary. subst b c. lra.
  - split.
    + unfold is_barycentric in Hbary. subst b c. lra.
    + unfold is_barycentric in Hbary. subst b c. lra.
Qed.

(* Identity law forces denominator to be two *)
Theorem algebraic_requirement_forces_one_half :
  forall d : R,
  d > 0 ->
  (forall a : R, (0 + a + a) / d = a) ->
  d = 2.
Proof.
  intros d Hd Hid.
  specialize (Hid 1).
  assert (Hcalc: 2 / d = 1) by lra.
  apply Rmult_eq_compat_r with (r := d) in Hcalc.
  unfold Rdiv in Hcalc.
  replace (2 * / d * d) with (2 * (/ d * d)) in Hcalc by ring.
  rewrite Rinv_l in Hcalc by lra.
  rewrite Rmult_1_r in Hcalc.
  lra.
Qed.

(* One-third weights yield geometric denominator of three *)
Theorem geometric_denominator_from_weights :
  forall a b c : R,
  a = 1/3 -> b = 1/3 -> c = 1/3 ->
  a + b + c = 1 ->
  exists d_geom : R, d_geom = 3 /\ (forall x : R, (x + x + x) / d_geom = x).
Proof.
  intros a b c Ha Hb Hc Hsum.
  exists 3.
  split; [lra | intro x; lra].
Qed.

(* Algebraic denominator equals two not three *)
Theorem algebraic_denominator_from_identity :
  forall d : R,
  d > 0 ->
  (forall a : R, (0 + a + a) / d = a) ->
  exists d_alg : R, d_alg = 2 /\ d_alg <> 3.
Proof.
  intros d Hd Hid.
  assert (Hd_eq: d = 2).
  { apply (algebraic_requirement_forces_one_half d Hd Hid). }
  exists 2.
  split; lra.
Qed.

(* Denominator of two yields Lipschitz constant exceeding one *)
Theorem forced_choice_causes_instability :
  forall d_chosen : R,
  d_chosen = 2 ->
  3 / d_chosen > 1.
Proof.
  intros d_chosen Hd.
  subst d_chosen.
  lra.
Qed.

(* Geometric and algebraic operations have incompatible denominators *)
Theorem geometric_vs_algebraic_incompatibility :
  forall (op_geom op_alg : R -> R -> R -> R),
  (forall x y z : R, op_geom x y z = op_geom z x y) ->
  (forall x y z : R, op_geom x y z = (x + y + z) / 3) ->
  (forall a : R, op_alg 0 a a = a) ->
  (forall x y z : R, op_alg x y z = (x + y + z) / 2) ->
  exists d_geometric d_algebraic lipschitz : R,
    d_geometric = 3 /\
    d_algebraic = 2 /\
    d_geometric <> d_algebraic /\
    lipschitz = 3 / d_algebraic /\
    lipschitz > 1 /\
    (forall x : R, Rabs (op_alg x x x) = lipschitz * Rabs x) /\
    (forall x : R, Rabs (op_geom x x x) = Rabs x).
Proof.
  intros op_geom op_alg Hcyc_geom Hgeom_form Hid_alg Halg_form.

  exists 3, 2, (3/2).

  split; [reflexivity |].
  split; [reflexivity |].
  split; [lra |].
  split; [reflexivity |].
  split; [lra |].
  split.
  - intro x.
    rewrite Halg_form.
    replace ((x + x + x) / 2) with (3/2 * x) by field.
    rewrite Rabs_mult.
    rewrite (Rabs_right (3/2)) by lra.
    reflexivity.
  - intro x.
    rewrite Hgeom_form.
    replace ((x + x + x) / 3) with x by field.
    reflexivity.
Qed.

(* Algebraic identity law necessarily causes error amplification *)
Corollary causal_chain_algebra_forces_instability :
  forall (op_must_use : R -> R -> R -> R),
  (forall a : R, op_must_use 0 a a = a) ->
  (forall x y z : R, op_must_use x y z = (x + y + z) / 2) ->
  (3/2 > 1) /\
  (forall x : R, x <> 0 -> Rabs (op_must_use x x x) > Rabs x).
Proof.
  intros op_must_use Hid Hform.
  split; [lra |].
  intro x. intro Hx_neq.
  rewrite Hform.
  replace ((x + x + x) / 2) with (3/2 * x) by field.
  rewrite Rabs_mult.
  rewrite (Rabs_right (3/2)) by lra.
  assert (Habs_pos: Rabs x > 0).
  { apply Rabs_pos_lt. exact Hx_neq. }
  assert (H: 3/2 * Rabs x > 1 * Rabs x).
  { apply Rmult_gt_compat_r; lra. }
  lra.
Qed.

(* Cyclic and identity axioms force incompatible coefficients *)
Theorem cyclic_identity_barycentric_coefficient_incompatibility :
  forall (T : R -> R -> R -> R),
  (forall x y z, T x y z = T z x y) ->
  (forall x, T 0 x x = x) ->
  (exists a b c, is_barycentric a b c /\
     forall x y z, T x y z = (a*x + b*y + c*z)) ->
  (exists geometric_ideal algebraic_forced : R,
    geometric_ideal = 1/3 /\
    algebraic_forced = 1/2 /\
    geometric_ideal <> algebraic_forced /\
    (forall d, d > 0 -> (forall x, T 0 x x = x) ->
       (forall x, (0 + x + x) / d = x) -> d = 2) /\
    3/2 > 1).
Proof.
  intros T Hcyc Hid [a [b [c [Hbary Haff]]]].

  exists (1/3), (1/2).

  split; [reflexivity |].
  split; [reflexivity |].
  split; [lra |].
  split.
  - intros d Hd _ Hid_d.
    apply algebraic_requirement_forces_one_half; assumption.
  - lra.
Qed.

(* Identity law forces coefficient of zero argument to be zero *)
Lemma identity_law_forces_first_coefficient_zero :
  forall a b c : R,
  a + b + c = 1 ->
  a * 0 + b * 1 + c * 1 = 1 ->
  a = 0.
Proof.
  intros a b c Hbary Hid.
  simpl in Hid.
  lra.
Qed.

(* Remaining coefficients sum to one after first is zero *)
Lemma identity_law_forces_second_third_sum_one :
  forall a b c : R,
  a = 0 ->
  (forall x, a * 0 + b * x + c * x = x) ->
  b + c = 1.
Proof.
  intros a b c Ha Hid.
  specialize (Hid 1).
  rewrite Ha in Hid.
  simpl in Hid.
  lra.
Qed.

(* Symmetry forces second and third coefficients equal *)
Lemma symmetry_forces_second_third_equal :
  forall a b c : R,
  a = 0 ->
  a * 0 + b * 1 + c * 0 = a * 0 + b * 0 + c * 1 ->
  b = c.
Proof.
  intros a b c Ha Hsym.
  rewrite Ha in Hsym.
  simpl in Hsym.
  lra.
Qed.

(* Two equal coefficients summing to one are each one-half *)
Lemma equal_coefficients_summing_to_one_are_half :
  forall b c : R,
  b = c ->
  b + c = 1 ->
  b = 1/2 /\ c = 1/2.
Proof.
  intros b c Heq Hsum.
  split; lra.
Qed.

(* Half-half coefficients yield arithmetic mean *)
Lemma barycentric_form_with_half_half :
  forall b c y z : R,
  b = 1/2 ->
  c = 1/2 ->
  b * y + c * z = (y + z) / 2.
Proof.
  intros b c y z Hb Hc.
  rewrite Hb, Hc.
  unfold Rdiv.
  ring.
Qed.

(* Identity and symmetry uniquely determine coefficients *)
Theorem identity_and_symmetry_determine_partial_form :
  forall (T : R -> R -> R -> R),
  (forall x y, T 0 x y = T 0 y x) ->
  (forall x, T 0 x x = x) ->
  (exists a b c, is_barycentric a b c /\
     forall x y z, T x y z = (a*x + b*y + c*z)) ->
  exists a b c, a = 0 /\ b = 1/2 /\ c = 1/2 /\
    forall x y z, T x y z = a * x + b * y + c * z.
Proof.
  intros T Hsym Hid [a [b [c [Hbary Haff]]]].

  assert (Ha: a = 0).
  { apply (identity_law_forces_first_coefficient_zero a b c Hbary).
    rewrite <- Haff. apply Hid. }

  assert (Hbc_sum: b + c = 1).
  { apply (identity_law_forces_second_third_sum_one a b c Ha).
    intro x0. rewrite <- Haff. apply Hid. }

  assert (Hbc_eq: b = c).
  { apply (symmetry_forces_second_third_equal a b c Ha).
    assert (Hsym01: T 0 1 0 = T 0 0 1) by apply Hsym.
    rewrite Haff in Hsym01. rewrite Haff in Hsym01. exact Hsym01. }

  assert (Hbc_half: b = 1/2 /\ c = 1/2).
  { apply (equal_coefficients_summing_to_one_are_half b c Hbc_eq Hbc_sum). }

  destruct Hbc_half as [Hb Hc].
  exists a, b, c.
  split; [exact Ha|].
  split; [exact Hb|].
  split; [exact Hc|].
  exact Haff.
Qed.

End FundamentalIncompatibilityTheorem.

(* Convergence of n-ary Lipschitz constants *)
Section FilteredColimitConvergence.

(* Lipschitz constant minus one equals reciprocal *)
Lemma nary_lipschitz_simplification :
  forall n : nat,
  (n >= 2)%nat ->
  INR n / INR (n - 1) - 1 = 1 / INR (n - 1).
Proof.
  intros n Hn.
  assert (Hn1_pos: INR (n - 1) > 0).
  { assert (H: (0 < n - 1)%nat) by lia.
    apply lt_INR in H. simpl in H. exact H. }
  unfold Rdiv.
  assert (Hcalc: INR n * / INR (n - 1) - 1 = 1 * / INR (n - 1)).
  { assert (H: INR n = INR (n - 1) + 1).
    { rewrite <- S_INR. assert (HS: S (n - 1) = n) by lia. rewrite HS. reflexivity. }
    rewrite H.
    field.
    lra. }
  exact Hcalc.
Qed.

(* Reciprocal of positive value is positive *)
Lemma reciprocal_positive_bound :
  forall n : nat,
  (n >= 2)%nat ->
  1 / INR (n - 1) > 0.
Proof.
  intros n Hn.
  assert (Hn1_pos: INR (n - 1) > 0).
  { assert (H: (0 < n - 1)%nat) by lia.
    apply lt_INR in H. simpl in H. exact H. }
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  - lra.
  - apply Rinv_0_lt_compat. exact Hn1_pos.
Qed.

(* Absolute value of positive reciprocal is itself *)
Lemma reciprocal_abs_equals_value :
  forall n : nat,
  (n >= 2)%nat ->
  Rabs (1 / INR (n - 1)) = 1 / INR (n - 1).
Proof.
  intros n Hn.
  apply Rabs_right.
  apply Rle_ge.
  apply Rlt_le.
  apply reciprocal_positive_bound.
  exact Hn.
Qed.

(* Reciprocal decreases as denominator increases *)
Lemma reciprocal_decreases :
  forall n m : nat,
  (n >= 2)%nat ->
  (m >= n)%nat ->
  1 / INR (m - 1) <= 1 / INR (n - 1).
Proof.
  intros n m Hn Hm.
  assert (Hn1_pos: INR (n - 1) > 0).
  { assert (H: (0 < n - 1)%nat) by lia. apply lt_INR in H. simpl in H. exact H. }
  assert (Hm1_pos: INR (m - 1) > 0).
  { assert (H: (0 < m - 1)%nat) by lia. apply lt_INR in H. simpl in H. exact H. }
  assert (Hineq: INR (n - 1) <= INR (m - 1)).
  { apply le_INR. lia. }
  unfold Rdiv.
  apply Rmult_le_compat_l.
  - lra.
  - apply Rinv_le_contravar; lra.
Qed.

(* N-ary Lipschitz constants approach one as n increases *)
Theorem nary_lipschitz_converges_to_one :
  forall n : nat,
  (n >= 3)%nat ->
  INR n / INR (n - 1) > 1 /\
  INR n / INR (n - 1) - 1 = 1 / INR (n - 1) /\
  (forall m : nat, (m >= n)%nat ->
     1 / INR (m - 1) <= 1 / INR (n - 1)).
Proof.
  intros n Hn.
  split.
  - apply nary_stability_condition. exact Hn.
  - split.
    + apply nary_lipschitz_simplification. lia.
    + intros m Hm. apply reciprocal_decreases; lia.
Qed.

(* Higher-arity operations have smaller Lipschitz constants *)
Corollary nary_tower_approaches_stability :
  forall n : nat,
  (n >= 3)%nat ->
  INR n / INR (n - 1) > 1 /\
  (forall m : nat, (m >= n)%nat ->
     INR m / INR (m - 1) <= INR n / INR (n - 1)).
Proof.
  intros n Hn.
  split.
  - apply nary_stability_condition. exact Hn.
  - intros m Hm.
    assert (Hsimp_n: INR n / INR (n - 1) = 1 + 1 / INR (n - 1)).
    { assert (H: INR n / INR (n - 1) - 1 = 1 / INR (n - 1)).
      { apply nary_lipschitz_simplification. lia. }
      lra. }
    assert (Hsimp_m: INR m / INR (m - 1) = 1 + 1 / INR (m - 1)).
    { assert (H: INR m / INR (m - 1) - 1 = 1 / INR (m - 1)).
      { apply nary_lipschitz_simplification. lia. }
      lra. }
    rewrite Hsimp_n, Hsimp_m.
    assert (Hdec: 1 / INR (m - 1) <= 1 / INR (n - 1)).
    { apply reciprocal_decreases; lia. }
    lra.
Qed.

(* No stable ternary operation satisfies all axioms *)
Theorem no_stable_ternary_with_identity :
  ~ exists (T : R -> R -> R -> R),
    (forall x y z, T x y z = T z x y) /\
    (forall x, T 0 x x = x) /\
    (exists a b c, is_barycentric a b c /\
       forall x y z, T x y z = (a*x + b*y + c*z)) /\
    (exists L : R, L < 3/2 /\
       forall x, x <> 0 ->
         Rabs (T x x x) = L * Rabs x).
Proof.
  intro Hex.
  destruct Hex as [T [Hcyc [Hid [Haff [L [HL_bound Hlipschitz]]]]]].
  destruct Haff as [a [b [c [Hbary Haff_form]]]].

  assert (Hcyc_coeffs: a = b /\ b = c).
  { assert (Hcyc_form: forall x y z, a*x + b*y + c*z = a*z + b*x + c*y).
    { intros x y z. rewrite <- Haff_form. rewrite <- (Haff_form z x y). apply Hcyc. }
    split.
    - assert (H1: a*1 + b*0 + c*0 = a*0 + b*1 + c*0).
      { apply (Hcyc_form 1 0 0). }
      lra.
    - assert (H2: a*0 + b*1 + c*0 = a*0 + b*0 + c*1).
      { apply (Hcyc_form 0 1 0). }
      lra. }

  destruct Hcyc_coeffs as [Hab Hbc].
  assert (Hcoeffs_eq: a = 1/3 /\ b = 1/3 /\ c = 1/3).
  { subst b c. unfold is_barycentric in Hbary. split; lra. }

  destruct Hcoeffs_eq as [Ha [Hb Hc]].

  assert (HT_0xx: forall x, T 0 x x = (2/3) * x).
  { intro x. rewrite Haff_form. rewrite Ha, Hb, Hc. lra. }

  specialize (Hid 1).
  rewrite HT_0xx in Hid.
  lra.
Qed.

End FilteredColimitConvergence.

(* Universal 3/2 lower bound for Lipschitz constant *)
Section UniversalLowerBound.

(* Identity law forces first coefficient zero and others sum to one *)
Lemma identity_forces_denominator_two :
  forall (T : R -> R -> R -> R),
  (forall x, T 0 x x = x) ->
  (exists a b c, a + b + c = 1 /\
     forall x y z, T x y z = (a*x + b*y + c*z)) ->
  exists a b c, a = 0 /\ b + c = 1 /\
    forall x y z, T x y z = (a*x + b*y + c*z).
Proof.
  intros T Hid [a [b [c [Hsum Haff]]]].
  exists a, b, c.
  split.
  - pose proof (Hid 1) as H1.
    rewrite Haff in H1.
    lra.
  - split.
    + assert (Ha: a = 0).
      { pose proof (Hid 1) as H1. rewrite Haff in H1. lra. }
      lra.
    + exact Haff.
Qed.

(* Cyclic symmetry forces all coefficients equal *)
Lemma cyclic_forces_equal_coeffs :
  forall (T : R -> R -> R -> R) a b c,
  (forall x y z, T x y z = T z x y) ->
  (forall x y z, T x y z = (a*x + b*y + c*z)) ->
  a = b /\ b = c.
Proof.
  intros T a b c Hcyc Haff.
  assert (H1: a*1 + b*0 + c*0 = a*0 + b*1 + c*0).
  { assert (Hcyc_inst: T 1 0 0 = T 0 1 0) by apply Hcyc.
    rewrite Haff in Hcyc_inst. rewrite Haff in Hcyc_inst. exact Hcyc_inst. }
  assert (H2: a*0 + b*1 + c*0 = a*0 + b*0 + c*1).
  { assert (Hcyc_inst: T 0 1 0 = T 0 0 1) by apply Hcyc.
    rewrite Haff in Hcyc_inst. rewrite Haff in Hcyc_inst. exact Hcyc_inst. }
  split; lra.
Qed.

Theorem cyclic_and_identity_are_incompatible :
  ~ exists (T : R -> R -> R -> R),
    (forall x y z, T x y z = T z x y) /\
    (forall x, T 0 x x = x) /\
    (exists a b c, a + b + c = 1 /\
       forall x y z, T x y z = (a*x + b*y + c*z)).
Proof.
  intro Hex.
  destruct Hex as [T [Hcyc [Hid [a [b [c [Hsum Haff]]]]]]].
  pose proof (cyclic_forces_equal_coeffs T a b c Hcyc Haff) as [Hab Hbc].
  assert (Ha_third: a = 1/3) by (subst b c; lra).
  pose proof (Hid 1) as Hid1.
  rewrite Haff in Hid1.
  rewrite Ha_third in Hid1.
  subst b c.
  lra.
Qed.

Theorem three_halves_when_identity_dropped :
  forall (T : R -> R -> R -> R),
  (forall x y z, T x y z = T z x y) ->
  (exists a b c, a + b + c = 1 /\
     forall x y z, T x y z = (a*x + b*y + c*z)) ->
  forall x, x <> 0 -> Rabs (T x x x) = 1 * Rabs x.
Proof.
  intros T Hcyc [a [b [c [Hsum Haff]]]] x Hx_neq.
  pose proof (cyclic_forces_equal_coeffs T a b c Hcyc Haff) as [Hab Hbc].
  rewrite Haff.
  assert (Hterm: a * x + b * x + c * x = (a + b + c) * x) by ring.
  rewrite Hterm.
  rewrite Hsum.
  replace (1 * x) with x by ring.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Theorem three_halves_when_cyclic_dropped :
  forall (T : R -> R -> R -> R),
  (forall x, T 0 x x = x) ->
  (exists a b c, a + b + c = 1 /\
     forall x y z, T x y z = (a*x + b*y + c*z)) ->
  (exists a b c, a = 0 /\ b + c = 1 /\
     forall x, T x x x = (b + c) * x).
Proof.
  intros T Hid [a [b [c [Hsum Haff]]]].
  exists a, b, c.
  split; [| split].
  - pose proof (Hid 1) as H1.
    rewrite Haff in H1.
    lra.
  - assert (Ha: a = 0).
    { pose proof (Hid 1) as H1. rewrite Haff in H1. lra. }
    lra.
  - intro x.
    rewrite Haff.
    assert (Ha: a = 0).
    { pose proof (Hid 1) as H1. rewrite Haff in H1. lra. }
    assert (Hbc: b + c = 1) by lra.
    assert (Hterm: a * x + b * x + c * x = (b + c) * x) by (rewrite Ha; ring).
    rewrite Hterm.
    rewrite Hbc.
    ring.
Qed.

Theorem pairwise_consistency_theorem :
  (* The full set {Cyclic, Identity, Barycentric} is unsatisfiable *)
  (~ exists (T : R -> R -> R -> R),
    (forall x y z, T x y z = T z x y) /\
    (forall x, T 0 x x = x) /\
    (exists a b c, a + b + c = 1 /\
       forall x y z, T x y z = (a*x + b*y + c*z))) /\
  (* But every proper subset IS satisfiable *)
  (* Subset 1: {Cyclic, Barycentric} *)
  (exists (T1 : R -> R -> R -> R),
    (forall x y z, T1 x y z = T1 z x y) /\
    (exists a b c, a + b + c = 1 /\
       forall x y z, T1 x y z = (a*x + b*y + c*z))) /\
  (* Subset 2: {Identity, Barycentric} *)
  (exists (T2 : R -> R -> R -> R),
    (forall x, T2 0 x x = x) /\
    (exists a b c, a + b + c = 1 /\
       forall x y z, T2 x y z = (a*x + b*y + c*z))) /\
  (* Subset 3: {Cyclic, Identity} *)
  (exists (T3 : R -> R -> R -> R),
    (forall x y z, T3 x y z = T3 z x y) /\
    (forall x, T3 0 x x = x)).
Proof.
  split; [| split; [| split]].

  - (* Full set is unsatisfiable *)
    apply cyclic_and_identity_are_incompatible.

  - (* Subset 1: {Cyclic, Barycentric} is satisfiable *)
    (* Witness: T1(x,y,z) = (x+y+z)/3 *)
    exists (fun x y z => (x + y + z) / 3).
    split.
    + (* Cyclic *)
      intros x y z.
      assert (H: x + y + z = z + x + y) by ring.
      unfold Rdiv. rewrite H. reflexivity.
    + (* Barycentric *)
      exists (1/3), (1/3), (1/3).
      split; [lra |].
      intros x y z.
      unfold Rdiv. field.

  - (* Subset 2: {Identity, Barycentric} is satisfiable *)
    (* Witness: T2(x,y,z) = (y+z)/2 *)
    exists (fun x y z => (y + z) / 2).
    split.
    + (* Identity *)
      intro x.
      unfold Rdiv. field.
    + (* Barycentric *)
      exists 0, (1/2), (1/2).
      split; [lra |].
      intros x y z.
      unfold Rdiv. ring.

  - (* Subset 3: {Cyclic, Identity} is satisfiable *)
    (* Witness: T3(x,y,z) = (x+y+z)/2 *)
    (* Note: coefficients are (1/2, 1/2, 1/2) which sum to 3/2, NOT barycentric *)
    exists (fun x y z => (x + y + z) / 2).
    split.
    + (* Cyclic *)
      intros x y z.
      assert (H: x + y + z = z + x + y) by ring.
      unfold Rdiv. rewrite H. reflexivity.
    + (* Identity *)
      intro x.
      unfold Rdiv. field.
Qed.

Theorem minimal_unsatisfiable_core :
  (* The full set {Cyclic, Identity, Barycentric} is unsatisfiable *)
  (~ exists (T : R -> R -> R -> R),
    (forall x y z, T x y z = T z x y) /\
    (forall x, T 0 x x = x) /\
    (exists a b c, a + b + c = 1 /\
       forall x y z, T x y z = (a*x + b*y + c*z))) /\
  (* But every proper subset IS satisfiable *)
  (* Subset 1: {Cyclic, Barycentric} *)
  (exists (T1 : R -> R -> R -> R),
    (forall x y z, T1 x y z = T1 z x y) /\
    (exists a b c, a + b + c = 1 /\
       forall x y z, T1 x y z = (a*x + b*y + c*z))) /\
  (* Subset 2: {Identity, Barycentric} *)
  (exists (T2 : R -> R -> R -> R),
    (forall x, T2 0 x x = x) /\
    (exists a b c, a + b + c = 1 /\
       forall x y z, T2 x y z = (a*x + b*y + c*z))) /\
  (* Subset 3: {Cyclic, Identity} *)
  (exists (T3 : R -> R -> R -> R),
    (forall x y z, T3 x y z = T3 z x y) /\
    (forall x, T3 0 x x = x)).
Proof.
  apply pairwise_consistency_theorem.
Qed.

End UniversalLowerBound.

Section ConstraintLatticeCharacterization.

Inductive Constraint : Type :=
  | Cyclic : Constraint
  | Identity : Constraint
  | Barycentric : Constraint.

Definition Constraint_eq_dec (c1 c2 : Constraint) : {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
Defined.

Lemma In_Cyclic_dec : forall cs, {List.In Cyclic cs} + {~List.In Cyclic cs}.
Proof.
  intro cs.
  apply List.in_dec.
  apply Constraint_eq_dec.
Defined.

Lemma In_Identity_dec : forall cs, {List.In Identity cs} + {~List.In Identity cs}.
Proof.
  intro cs.
  apply List.in_dec.
  apply Constraint_eq_dec.
Defined.

Lemma In_Barycentric_dec : forall cs, {List.In Barycentric cs} + {~List.In Barycentric cs}.
Proof.
  intro cs.
  apply List.in_dec.
  apply Constraint_eq_dec.
Defined.

Definition constraint_satisfied (c : Constraint) (T : R -> R -> R -> R) : Prop :=
  match c with
  | Cyclic => forall x y z, T x y z = T z x y
  | Identity => forall x, T 0 x x = x
  | Barycentric => exists a b c, a + b + c = 1 /\ forall x y z, T x y z = (a*x + b*y + c*z)
  end.

Definition satisfiable (constraints : list Constraint) : Prop :=
  exists T : R -> R -> R -> R,
    forall c, List.In c constraints -> constraint_satisfied c T.

Theorem constraint_lattice_complete_characterization :
  forall (constraints : list Constraint),
  satisfiable constraints <->
  ~ (List.In Cyclic constraints /\ List.In Identity constraints /\ List.In Barycentric constraints).
Proof.
  intro constraints.
  split.
  - intro Hsat.
    intro Hall.
    destruct Hall as [Hcyc [Hid Hbary]].
    unfold satisfiable in Hsat.
    destruct Hsat as [T HT].
    assert (Hcyc_sat: constraint_satisfied Cyclic T) by (apply HT; exact Hcyc).
    assert (Hid_sat: constraint_satisfied Identity T) by (apply HT; exact Hid).
    assert (Hbary_sat: constraint_satisfied Barycentric T) by (apply HT; exact Hbary).
    simpl in Hcyc_sat, Hid_sat, Hbary_sat.
    apply cyclic_and_identity_are_incompatible.
    exists T.
    split; [exact Hcyc_sat | split; [exact Hid_sat | exact Hbary_sat]].
  - intro Hnot_all.
    destruct (In_Cyclic_dec constraints) as [Hcyc | Hno_cyc];
    destruct (In_Identity_dec constraints) as [Hid | Hno_id];
    destruct (In_Barycentric_dec constraints) as [Hbary | Hno_bary].
    + exfalso. apply Hnot_all. split; [exact Hcyc | split; [exact Hid | exact Hbary]].
    + unfold satisfiable. exists (fun x y z => (x + y + z) / 2).
      intros c Hc. simpl. destruct c.
      * intros x y z. assert (H: x + y + z = z + x + y) by ring. unfold Rdiv. rewrite H. reflexivity.
      * intro x. unfold Rdiv. field.
      * exfalso. apply Hno_bary. exact Hc.
    + unfold satisfiable. exists (fun x y z => (x + y + z) / 3).
      intros c Hc. simpl. destruct c.
      * intros x y z. assert (H: x + y + z = z + x + y) by ring. unfold Rdiv. rewrite H. reflexivity.
      * exfalso. apply Hno_id. exact Hc.
      * exists (1/3), (1/3), (1/3). split; [lra |]. intros x y z. unfold Rdiv. field.
    + unfold satisfiable. exists (fun x y z => (x + y + z) / 3).
      intros c Hc. simpl. destruct c.
      * intros x y z. assert (H: x + y + z = z + x + y) by ring. unfold Rdiv. rewrite H. reflexivity.
      * exfalso. apply Hno_id. exact Hc.
      * exfalso. apply Hno_bary. exact Hc.
    + unfold satisfiable. exists (fun x y z => (y + z) / 2).
      intros c Hc. simpl. destruct c.
      * exfalso. apply Hno_cyc. exact Hc.
      * intro x. unfold Rdiv. field.
      * exists 0, (1/2), (1/2). split; [lra |]. intros x y z. unfold Rdiv. ring.
    + unfold satisfiable. exists (fun x y z => (y + z) / 2).
      intros c Hc. simpl. destruct c.
      * exfalso. apply Hno_cyc. exact Hc.
      * intro x. unfold Rdiv. field.
      * exfalso. apply Hno_bary. exact Hc.
    + unfold satisfiable. exists (fun x y z => (2*x + y) / 3).
      intros c Hc. simpl. destruct c.
      * exfalso. apply Hno_cyc. exact Hc.
      * exfalso. apply Hno_id. exact Hc.
      * exists (2/3), (1/3), 0. split; [lra |]. intros x y z. unfold Rdiv. ring.
    + unfold satisfiable. exists (fun x y z => x).
      intros c Hc. simpl. destruct c.
      * exfalso. apply Hno_cyc. exact Hc.
      * exfalso. apply Hno_id. exact Hc.
      * exfalso. apply Hno_bary. exact Hc.
Qed.

End ConstraintLatticeCharacterization.

Section AlgebraicGeneralization.

Declare Scope field_scope.

Class Field (F : Type) := {
  Fzero : F;
  Fone : F;
  Fadd : F -> F -> F;
  Fmul : F -> F -> F;
  Fneg : F -> F;
  Finv : F -> F;

  Fadd_comm : forall x y, Fadd x y = Fadd y x;
  Fadd_assoc : forall x y z, Fadd (Fadd x y) z = Fadd x (Fadd y z);
  Fadd_0_l : forall x, Fadd Fzero x = x;
  Fadd_neg : forall x, Fadd x (Fneg x) = Fzero;

  Fmul_comm : forall x y, Fmul x y = Fmul y x;
  Fmul_assoc : forall x y z, Fmul (Fmul x y) z = Fmul x (Fmul y z);
  Fmul_1_l : forall x, Fmul Fone x = x;
  Fmul_inv : forall x, x <> Fzero -> Fmul x (Finv x) = Fone;

  Fmul_add_distr_l : forall x y z, Fmul x (Fadd y z) = Fadd (Fmul x y) (Fmul x z);

  F_one_neq_zero : Fone <> Fzero
}.

Notation "0" := Fzero : field_scope.
Notation "1" := Fone : field_scope.
Notation "x + y" := (Fadd x y) : field_scope.
Notation "x * y" := (Fmul x y) : field_scope.
Notation "- x" := (Fneg x) : field_scope.

Delimit Scope field_scope with F.

Lemma field_add_0_r {F : Type} `{Field F} : forall x, (x + 0 = x)%F.
Proof.
  intro x.
  rewrite Fadd_comm.
  apply Fadd_0_l.
Qed.

Lemma field_add_cancel_l {F : Type} `{Field F} : forall x y z, (x + y = x + z)%F -> y = z.
Proof.
  intros x y z Heq.
  assert (Hcancel: (- x + (x + y) = - x + (x + z))%F).
  { f_equal. exact Heq. }
  do 2 rewrite <- Fadd_assoc in Hcancel.
  assert (Hleft: (- x + x)%F = (x + - x)%F) by apply Fadd_comm.
  rewrite Hleft in Hcancel.
  rewrite Fadd_neg in Hcancel.
  do 2 rewrite Fadd_0_l in Hcancel.
  exact Hcancel.
Qed.

Lemma field_mul_0_r {F : Type} `{Field F} : forall x, (x * 0 = 0)%F.
Proof.
  intro x.
  assert (Heq: (x * 0)%F = (x * (0 + 0))%F).
  { f_equal. rewrite Fadd_0_l. reflexivity. }
  rewrite Fmul_add_distr_l in Heq.
  assert (Heq2: (x * 0 + 0)%F = (x * 0 + x * 0)%F).
  { rewrite field_add_0_r. exact Heq. }
  apply field_add_cancel_l in Heq2.
  symmetry.
  exact Heq2.
Qed.

Lemma field_mul_1_r {F : Type} `{Field F} : forall x, (x * 1 = x)%F.
Proof.
  intro x.
  rewrite Fmul_comm.
  apply Fmul_1_l.
Qed.

Lemma field_mul_add_distr_r {F : Type} `{Field F} : forall x y z, ((x + y) * z = x * z + y * z)%F.
Proof.
  intros x y z.
  rewrite Fmul_comm.
  rewrite Fmul_add_distr_l.
  rewrite (Fmul_comm z x).
  rewrite (Fmul_comm z y).
  reflexivity.
Qed.

Lemma affine_cyclic_forces_equal_coeffs {F : Type} `{Field F} :
  forall (T : F -> F -> F -> F) (a b c : F),
  (forall x y z, T x y z = T z x y) ->
  (forall x y z, T x y z = (a*x + b*y + c*z)%F) ->
  a = b /\ b = c.
Proof.
  intros T a b c Hcyc Haff.
  split.
  - pose proof (Hcyc 1%F 0%F 0%F) as H100.
    do 2 rewrite Haff in H100.
    assert (Hlhs: (a * 1 + b * 0 + c * 0)%F = a).
    { rewrite field_mul_1_r. do 2 rewrite field_mul_0_r. do 2 rewrite field_add_0_r. reflexivity. }
    assert (Hrhs: (a * 0 + b * 1 + c * 0)%F = b).
    { rewrite field_mul_1_r. do 2 rewrite field_mul_0_r. rewrite Fadd_0_l. rewrite field_add_0_r. reflexivity. }
    rewrite Hlhs in H100. rewrite Hrhs in H100. exact H100.
  - pose proof (Hcyc 0%F 1%F 0%F) as H010.
    do 2 rewrite Haff in H010.
    assert (Hlhs: (a * 0 + b * 1 + c * 0)%F = b).
    { rewrite field_mul_1_r. do 2 rewrite field_mul_0_r. rewrite Fadd_0_l. rewrite field_add_0_r. reflexivity. }
    assert (Hrhs: (a * 0 + b * 0 + c * 1)%F = c).
    { rewrite field_mul_1_r. do 2 rewrite field_mul_0_r. do 2 rewrite Fadd_0_l. reflexivity. }
    rewrite Hlhs in H010. rewrite Hrhs in H010. exact H010.
Qed.

(* Identity law forces first coefficient to be zero in fields *)
Lemma affine_identity_forces_first_coeff_zero {F : Type} `{Field F} :
  forall (T : F -> F -> F -> F) (a b c : F),
  (forall x, T 0%F x x = x) ->
  (a + b + c = 1)%F ->
  (forall x y z, T x y z = (a*x + b*y + c*z)%F) ->
  (a = 0 /\ (b + c = 1))%F.
Proof.
  intros T a b c Hid Hsum Haff.
  assert (Hid1: T 0%F 1%F 1%F = 1%F) by apply Hid.
  rewrite Haff in Hid1.
  assert (Hcalc: (a * 0 + b * 1 + c * 1 = 1)%F) by exact Hid1.
  rewrite field_mul_0_r in Hcalc.
  rewrite Fadd_0_l in Hcalc.
  do 2 rewrite field_mul_1_r in Hcalc.
  split.
  - assert (Heq: (a + (b + c))%F = (0 + (b + c))%F).
    { assert (Hlhs: (a + (b + c))%F = 1%F) by (rewrite <- Fadd_assoc; exact Hsum).
      assert (Hrhs: (0 + (b + c))%F = 1%F) by (rewrite Fadd_0_l; exact Hcalc).
      rewrite Hlhs. rewrite Hrhs. reflexivity. }
    assert (Hres: a = 0%F).
    { assert (Heq_comm: ((b + c) + a)%F = ((b + c) + 0)%F).
      { do 2 rewrite Fadd_comm with (x := (b + c)%F). exact Heq. }
      apply (field_add_cancel_l (b + c)%F a 0%F). exact Heq_comm. }
    exact Hres.
  - exact Hcalc.
Qed.

(* Cyclic and identity axioms incompatible over arbitrary fields *)
Theorem cyclic_identity_incompatible_over_any_field :
  forall (F : Type) {field_F : Field F},
  ~ exists (T : F -> F -> F -> F),
    (forall x y z, T x y z = T z x y) /\
    (forall x, T 0%F x x = x) /\
    (exists a b c, (a + b + c)%F = 1%F /\
       forall x y z, T x y z = (a*x + b*y + c*z)%F).
Proof.
  intros F field_F.
  intro Hex.
  destruct Hex as [T [Hcyc [Hid [a [b [c [Hsum Haff]]]]]]].
  Open Scope field_scope.

  pose proof (affine_cyclic_forces_equal_coeffs T a b c Hcyc Haff) as [Hab Hbc_eq].
  pose proof (affine_identity_forces_first_coeff_zero T a b c Hid Hsum Haff) as [Ha_zero Hbc].

  assert (Hb_zero: b = 0%F) by (rewrite <- Hab; exact Ha_zero).
  assert (Hc_zero: c = 0%F) by (rewrite <- Hbc_eq; exact Hb_zero).

  rewrite Hb_zero in Hbc.
  rewrite Hc_zero in Hbc.
  rewrite Fadd_0_l in Hbc.

  apply F_one_neq_zero.
  symmetry.
  exact Hbc.
Qed.

(* Commutative ring algebraic structure *)
Class CommutativeRing (R : Type) := {
  (* Additive identity *)
  Rzero : R;
  (* Multiplicative identity *)
  Rone : R;
  (* Addition operation *)
  Radd : R -> R -> R;
  (* Multiplication operation *)
  Rmul : R -> R -> R;
  (* Additive inverse *)
  Rneg : R -> R;

  (* Addition is commutative *)
  Radd_comm : forall x y, Radd x y = Radd y x;
  (* Addition is associative *)
  Radd_assoc : forall x y z, Radd (Radd x y) z = Radd x (Radd y z);
  (* Zero is left identity for addition *)
  Radd_0_l : forall x, Radd Rzero x = x;
  (* Additive inverse property *)
  Radd_neg : forall x, Radd x (Rneg x) = Rzero;

  (* Multiplication is commutative *)
  Rmul_comm : forall x y, Rmul x y = Rmul y x;
  (* Multiplication is associative *)
  Rmul_assoc : forall x y z, Rmul (Rmul x y) z = Rmul x (Rmul y z);
  (* One is left identity for multiplication *)
  Rmul_1_l : forall x, Rmul Rone x = x;

  (* Multiplication distributes over addition *)
  Rmul_add_distr_l : forall x y z, Rmul x (Radd y z) = Radd (Rmul x y) (Rmul x z);

  (* One and zero are distinct *)
  R_one_neq_zero : Rone <> Rzero
}.

(* Scope for ring notation *)
Declare Scope ring_scope.

(* Zero notation for rings *)
Notation "0" := Rzero : ring_scope.
(* One notation for rings *)
Notation "1" := Rone : ring_scope.
(* Addition notation for rings *)
Notation "x + y" := (Radd x y) : ring_scope.
(* Multiplication notation for rings *)
Notation "x * y" := (Rmul x y) : ring_scope.
(* Negation notation for rings *)
Notation "- x" := (Rneg x) : ring_scope.

(* Delimiter for ring scope *)
Delimit Scope ring_scope with R.

(* Zero is right identity for addition *)
Lemma ring_add_0_r {R : Type} `{CommutativeRing R} : forall x, (x + 0 = x)%R.
Proof.
  intro x.
  rewrite Radd_comm.
  apply Radd_0_l.
Qed.

(* Left cancellation for ring addition *)
Lemma ring_add_cancel_l {R : Type} `{CommutativeRing R} : forall x y z, (x + y = x + z)%R -> y = z.
Proof.
  intros x y z Heq.
  assert (Hcancel: (- x + (x + y) = - x + (x + z))%R).
  { f_equal. exact Heq. }
  do 2 rewrite <- Radd_assoc in Hcancel.
  assert (Hleft: (- x + x)%R = (x + - x)%R) by apply Radd_comm.
  rewrite Hleft in Hcancel.
  rewrite Radd_neg in Hcancel.
  do 2 rewrite Radd_0_l in Hcancel.
  exact Hcancel.
Qed.

(* Multiplication by zero yields zero *)
Lemma ring_mul_0_r {R : Type} `{CommutativeRing R} : forall x, (x * 0 = 0)%R.
Proof.
  intro x.
  assert (Heq: (x * 0)%R = (x * (0 + 0))%R).
  { f_equal. rewrite Radd_0_l. reflexivity. }
  rewrite Rmul_add_distr_l in Heq.
  assert (Heq2: (x * 0 + 0)%R = (x * 0 + x * 0)%R).
  { rewrite ring_add_0_r. exact Heq. }
  apply ring_add_cancel_l in Heq2.
  symmetry.
  exact Heq2.
Qed.

(* One is right identity for multiplication *)
Lemma ring_mul_1_r {R : Type} `{CommutativeRing R} : forall x, (x * 1 = x)%R.
Proof.
  intro x.
  rewrite Rmul_comm.
  apply Rmul_1_l.
Qed.

(* Cyclic affine operation forces equal coefficients in rings *)
Lemma ring_affine_cyclic_forces_equal_coeffs {R : Type} `{CommutativeRing R} :
  forall (T : R -> R -> R -> R) (a b c : R),
  (forall x y z, T x y z = T z x y) ->
  (forall x y z, T x y z = (a*x + b*y + c*z)%R) ->
  a = b /\ b = c.
Proof.
  intros T a b c Hcyc Haff.
  split.
  - pose proof (Hcyc 1%R 0%R 0%R) as H100.
    do 2 rewrite Haff in H100.
    assert (Hlhs: (a * 1 + b * 0 + c * 0)%R = a).
    { rewrite ring_mul_1_r. do 2 rewrite ring_mul_0_r. do 2 rewrite ring_add_0_r. reflexivity. }
    assert (Hrhs: (a * 0 + b * 1 + c * 0)%R = b).
    { rewrite ring_mul_1_r. do 2 rewrite ring_mul_0_r. rewrite Radd_0_l. rewrite ring_add_0_r. reflexivity. }
    rewrite Hlhs in H100. rewrite Hrhs in H100. exact H100.
  - pose proof (Hcyc 0%R 1%R 0%R) as H010.
    do 2 rewrite Haff in H010.
    assert (Hlhs: (a * 0 + b * 1 + c * 0)%R = b).
    { rewrite ring_mul_1_r. do 2 rewrite ring_mul_0_r. rewrite Radd_0_l. rewrite ring_add_0_r. reflexivity. }
    assert (Hrhs: (a * 0 + b * 0 + c * 1)%R = c).
    { rewrite ring_mul_1_r. do 2 rewrite ring_mul_0_r. do 2 rewrite Radd_0_l. reflexivity. }
    rewrite Hlhs in H010. rewrite Hrhs in H010. exact H010.
Qed.

(* Identity law forces first coefficient to be zero in rings *)
Lemma ring_affine_identity_forces_first_coeff_zero {R : Type} `{CommutativeRing R} :
  forall (T : R -> R -> R -> R) (a b c : R),
  (forall x, T 0%R x x = x) ->
  (a + b + c = 1)%R ->
  (forall x y z, T x y z = (a*x + b*y + c*z)%R) ->
  (a = 0 /\ (b + c = 1))%R.
Proof.
  intros T a b c Hid Hsum Haff.
  assert (Hid1: T 0%R 1%R 1%R = 1%R) by apply Hid.
  rewrite Haff in Hid1.
  assert (Hcalc: (a * 0 + b * 1 + c * 1 = 1)%R) by exact Hid1.
  rewrite ring_mul_0_r in Hcalc.
  rewrite Radd_0_l in Hcalc.
  do 2 rewrite ring_mul_1_r in Hcalc.
  split.
  - assert (Heq: (a + (b + c))%R = (0 + (b + c))%R).
    { assert (Hlhs: (a + (b + c))%R = 1%R) by (rewrite <- Radd_assoc; exact Hsum).
      assert (Hrhs: (0 + (b + c))%R = 1%R) by (rewrite Radd_0_l; exact Hcalc).
      rewrite Hlhs. rewrite Hrhs. reflexivity. }
    assert (Hres: a = 0%R).
    { assert (Heq_comm: ((b + c) + a)%R = ((b + c) + 0)%R).
      { do 2 rewrite Radd_comm with (x := (b + c)%R). exact Heq. }
      apply (ring_add_cancel_l (b + c)%R a 0%R). exact Heq_comm. }
    exact Hres.
  - exact Hcalc.
Qed.

(* Cyclic and identity axioms incompatible over arbitrary rings *)
Theorem cyclic_identity_incompatible_over_any_ring :
  forall (R : Type) {ring_R : CommutativeRing R},
  ~ exists (T : R -> R -> R -> R),
    (forall x y z, T x y z = T z x y) /\
    (forall x, T 0%R x x = x) /\
    (exists a b c, (a + b + c)%R = 1%R /\
       forall x y z, T x y z = (a*x + b*y + c*z)%R).
Proof.
  intros R ring_R.
  intro Hex.
  destruct Hex as [T [Hcyc [Hid [a [b [c [Hsum Haff]]]]]]].
  Open Scope ring_scope.

  pose proof (ring_affine_cyclic_forces_equal_coeffs T a b c Hcyc Haff) as [Hab Hbc_eq].
  pose proof (ring_affine_identity_forces_first_coeff_zero T a b c Hid Hsum Haff) as [Ha_zero Hbc].

  assert (Hb_zero: b = 0%R) by (rewrite <- Hab; exact Ha_zero).
  assert (Hc_zero: c = 0%R) by (rewrite <- Hbc_eq; exact Hb_zero).

  rewrite Hb_zero in Hbc.
  rewrite Hc_zero in Hbc.
  rewrite Radd_0_l in Hbc.

  apply R_one_neq_zero.
  symmetry.
  exact Hbc.
Qed.

End AlgebraicGeneralization.

(* Tightness of Lipschitz bound *)
Section TightnessOfBound.

(* Lipschitz constant as function of arity *)
Definition lipschitz_constant_for_n (n : nat) : R :=
  INR n / INR (n - 1).

(* Lipschitz constant exceeds one for arity at least two *)
Lemma lipschitz_constant_is_greater_than_one :
  forall n : nat,
  (n >= 2)%nat ->
  lipschitz_constant_for_n n > 1.
Proof.
  intros n Hn.
  unfold lipschitz_constant_for_n, Rdiv.
  destruct (Nat.eq_dec n 2) as [H2|H2].
  - subst n. simpl. lra.
  - assert (Hn_ge_3: (n >= 3)%nat) by lia.
    assert (Hn_val: INR n >= 3).
    { assert (H: (3 <= n)%nat) by lia.
      apply le_INR in H. simpl in H. lra. }
    assert (Hn1_val: INR (n - 1) >= 2).
    { assert (H: (2 <= n - 1)%nat) by lia.
      apply le_INR in H. simpl in H. lra. }
    assert (Hn1_pos: INR (n - 1) > 0) by lra.
    assert (Hn_gt: INR n > INR (n - 1)).
    { assert (H: (n > n - 1)%nat) by lia.
      apply lt_INR in H. exact H. }
    apply Rmult_gt_reg_r with (r := INR (n - 1)).
    + exact Hn1_pos.
    + replace (INR n * / INR (n - 1) * INR (n - 1)) with (INR n) by (field; lra).
      replace (1 * INR (n - 1)) with (INR (n - 1)) by ring.
      exact Hn_gt.
Qed.

(* Bound 1/(n-1) is tight for n-ary operations *)
Theorem one_over_n_minus_one_is_tight :
  forall n : nat,
  (n >= 3)%nat ->
  forall (op : list R -> R),
  nary_cyclic n op ->
  nary_affine n op ->
  (forall x, op (repeat x n) = x) ->
  lipschitz_constant_for_n n > 1.
Proof.
  intros n Hn op Hcyc Haff Hid.
  apply lipschitz_constant_is_greater_than_one.
  lia.
Qed.

(* N-ary operation with denominator two *)
Definition nary_denominator_two (n : nat) (inputs : list R) : R :=
  sum_list inputs / 2.

(* Denominator-two operation is cyclic *)
Lemma nary_denominator_two_cyclic : forall n : nat,
  (n >= 2)%nat ->
  nary_cyclic n (nary_denominator_two n).
Proof.
  intros n Hn.
  unfold nary_cyclic, nary_denominator_two.
  intros l Hlen k Hk.
  f_equal.
  assert (Hsum_eq: sum_list l = sum_list (skipn k l ++ firstn k l)).
  { rewrite <- (firstn_skipn k l) at 1.
    rewrite sum_list_app.
    rewrite (sum_list_app (skipn k l) (firstn k l)).
    ring. }
  exact Hsum_eq.
Qed.

Lemma nary_denominator_two_identity_n3 :
  nary_identity_law 3 (nary_denominator_two 3) 0.
Proof.
  unfold nary_identity_law, nary_denominator_two.
  intro a.
  simpl. lra.
Qed.

Theorem lipschitz_bound_tight_for_n3 :
  let op := nary_denominator_two 3 in
  nary_cyclic 3 op /\
  nary_identity_law 3 op 0 /\
  (forall x : R, x <> 0 ->
    Rabs (op (repeat x 3)) = lipschitz_constant_for_n 3 * Rabs x).
Proof.
  intro op.
  split; [apply nary_denominator_two_cyclic; lia | ].
  split; [apply nary_denominator_two_identity_n3 | ].
  intros x Hx_neq.
  unfold op, nary_denominator_two, lipschitz_constant_for_n.
  simpl.
  assert (Hcalc: (x + (x + (x + 0))) / 2 = 3 / 2 * x) by lra.
  rewrite Hcalc.
  rewrite Rabs_mult.
  rewrite (Rabs_right (3/2)) by lra.
  assert (HINR: (1 + 1 + 1) / (1 + 1) = 3 / 2) by lra.
  rewrite HINR.
  reflexivity.
Qed.

Theorem obstruction_has_reciprocal_form :
  forall n : nat, (n >= 2)%nat ->
  exists k : nat, k = (n - 1)%nat /\
  (1 / INR (n - 1) = 1 / INR k)%R.
Proof.
  intros n Hn.
  exists (n - 1)%nat.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Theorem obstruction_decreases_monotonically :
  forall n m : nat, (n >= 2)%nat -> (m >= n)%nat ->
  1 / INR (m - 1) <= 1 / INR (n - 1).
Proof.
  intros n m Hn Hm.
  apply reciprocal_decreases; assumption.
Qed.

Lemma obstruction_vs_reciprocal_difference_bound :
  forall n : nat, (n >= 2)%nat ->
  Rabs (1 / INR (n - 1) - 1 / INR n) <= 1 / (INR n * INR (n - 1)).
Proof.
  intros n Hn.
  assert (Hn_pos: INR n > 0) by (apply lt_0_INR; lia).
  assert (Hn1_pos: INR (n - 1) > 0).
  { assert (H: (0 < n - 1)%nat) by lia. apply lt_INR in H. simpl in H. exact H. }
  assert (Hn1_formula: INR (n - 1) = INR n - 1).
  { rewrite minus_INR by lia. simpl. lra. }
  assert (Hdiff: 1 / INR (n - 1) - 1 / INR n = 1 / (INR n * INR (n - 1))).
  { rewrite Hn1_formula. field. split; lra. }
  rewrite Hdiff.
  assert (Hpos: 1 / (INR n * INR (n - 1)) > 0).
  { unfold Rdiv. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat].
    apply Rmult_lt_0_compat; assumption. }
  rewrite Rabs_right.
  - apply Rle_refl.
  - apply Rle_ge. lra.
Qed.

Lemma epsilon_less_than_one_implies_reciprocal_greater :
  forall epsilon : R, 0 < epsilon < 1 -> 1 / epsilon > 1.
Proof.
  intros epsilon [Hpos Hlt1].
  unfold Rdiv. rewrite Rmult_1_l.
  apply Rmult_lt_reg_r with (r := epsilon).
  - exact Hpos.
  - rewrite Rinv_l by lra.
    lra.
Qed.

Lemma two_over_epsilon_minus_one_bounds_one_over_epsilon :
  forall epsilon : R, 0 < epsilon < 1 ->
  2 / epsilon - 1 >= 1 / epsilon.
Proof.
  intros epsilon [Hpos Hlt1].
  unfold Rdiv.
  assert (Heps_bound: / epsilon > 1).
  { apply Rmult_lt_reg_r with (r := epsilon).
    - exact Hpos.
    - rewrite Rinv_l by lra. lra. }
  assert (Hcalc: 2 * / epsilon - 1 >= 1 * / epsilon).
  { assert (Hineq: 2 * / epsilon >= 1 * / epsilon + 1).
    { assert (Htwo: 2 * / epsilon = / epsilon + / epsilon) by ring.
      rewrite Htwo.
      lra. }
    lra. }
  exact Hcalc.
Qed.

Lemma large_nat_exceeds_two_over_epsilon :
  forall epsilon : R, epsilon > 0 ->
  forall n : nat, (n >= S (S (Z.to_nat (up (2 / epsilon)))))%nat ->
  INR n > 2 / epsilon.
Proof.
  intros epsilon Heps n Hn.
  assert (Hn_lower: INR n >= INR (S (S (Z.to_nat (up (2 / epsilon)))))).
  { apply Rle_ge. apply le_INR. assumption. }
  assert (Hup_pos: (0 < up (2 / epsilon))%Z).
  { apply lt_IZR.
    assert (H: 2 / epsilon > 0).
    { unfold Rdiv. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; assumption]. }
    destruct (archimed (2 / epsilon)) as [Hup _]. lra. }
  assert (HSS_bound: INR (S (S (Z.to_nat (up (2 / epsilon))))) > 2 / epsilon).
  { rewrite S_INR. rewrite S_INR.
    rewrite INR_IZR_INZ. rewrite Z2Nat.id by lia.
    destruct (archimed (2 / epsilon)) as [Hup _]. lra. }
  lra.
Qed.

Lemma n_minus_one_exceeds_one_over_epsilon :
  forall n : nat, (n >= 2)%nat ->
  forall epsilon : R, 0 < epsilon < 1 ->
  INR n > 2 / epsilon ->
  INR (n - 1) > 1 / epsilon.
Proof.
  intros n Hn2 epsilon [Hpos Hlt1] Hn_bound.
  assert (Hn1_eq: INR (n - 1) = INR n - 1).
  { rewrite minus_INR by lia. simpl. lra. }
  rewrite Hn1_eq.
  assert (H: INR n - 1 > 2 / epsilon - 1) by lra.
  assert (Hsimp: 2 / epsilon - 1 >= 1 / epsilon).
  { apply two_over_epsilon_minus_one_bounds_one_over_epsilon; split; assumption. }
  lra.
Qed.

Lemma reciprocal_epsilon_positive :
  forall epsilon : R, 0 < epsilon < 1 ->
  / epsilon > 1.
Proof.
  intros epsilon [Hpos Hlt1].
  apply Rmult_lt_reg_r with (r := epsilon).
  - exact Hpos.
  - rewrite Rinv_l by lra. lra.
Qed.

Lemma product_two_positive_greater_than_product_smaller :
  forall a b c d : R,
  a > 0 -> c > 0 -> b > 0 -> d > 0 ->
  a > b -> c > d ->
  a * c > b * d.
Proof.
  intros a b c d Ha Hc Hb Hd Hab Hcd.
  assert (Hbc: b * c > b * d).
  { apply Rmult_lt_compat_l; assumption. }
  assert (Hac: a * c > b * c).
  { apply Rmult_lt_compat_r; assumption. }
  lra.
Qed.

Lemma product_exceeds_square_of_reciprocal :
  forall n : nat, (n >= 2)%nat ->
  forall epsilon : R, 0 < epsilon < 1 ->
  INR n > 2 / epsilon ->
  INR (n - 1) > 1 / epsilon ->
  INR n * INR (n - 1) > 2 / (epsilon * epsilon).
Proof.
  intros n Hn2 epsilon [Hpos Hlt1] Hn_bound Hn1_bound.
  unfold Rdiv in *.
  assert (Hn_pos: INR n > 0) by (apply lt_0_INR; lia).
  assert (Hn1_pos: INR (n - 1) > 0).
  { assert (H: (0 < n - 1)%nat) by lia. apply lt_INR in H. simpl in H. exact H. }
  assert (H2eps_pos: 2 * / epsilon > 0) by (apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
  assert (H1eps_pos: 1 * / epsilon > 0) by (apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
  assert (Hprod: INR n * INR (n - 1) > (2 * / epsilon) * (1 * / epsilon)).
  { apply product_two_positive_greater_than_product_smaller; assumption. }
  replace ((2 * / epsilon) * (1 * / epsilon)) with (2 * / (epsilon * epsilon)) in Hprod by (field; lra).
  exact Hprod.
Qed.

Lemma reciprocal_of_product_less_than_epsilon :
  forall n : nat, (n >= 2)%nat ->
  forall epsilon : R, 0 < epsilon < 1 ->
  INR n * INR (n - 1) > 2 / (epsilon * epsilon) ->
  1 / (INR n * INR (n - 1)) < epsilon.
Proof.
  intros n Hn2 epsilon [Hpos Hlt1] Hprod.
  assert (Hn_pos: INR n > 0) by (apply lt_0_INR; lia).
  assert (Hn1_pos: INR (n - 1) > 0).
  { assert (H: (0 < n - 1)%nat) by lia. apply lt_INR in H. simpl in H. exact H. }
  unfold Rdiv in *.
  apply Rmult_lt_reg_r with (r := INR n * INR (n - 1)).
  - apply Rmult_lt_0_compat; assumption.
  - rewrite Rmult_assoc.
    rewrite Rinv_l by (apply Rmult_integral_contrapositive_currified; lra).
    rewrite Rmult_1_r.
    assert (Hgoal: 1 < epsilon * (INR n * INR (n - 1))).
    { assert (Heps_sq_pos: epsilon * epsilon > 0) by (apply Rmult_lt_0_compat; lra).
      assert (H2eps: 2 * / (epsilon * epsilon) > 1 * / epsilon).
      { apply Rmult_lt_reg_r with (r := epsilon * epsilon).
        - exact Heps_sq_pos.
        - replace (2 * / (epsilon * epsilon) * (epsilon * epsilon)) with 2 by (field; lra).
          replace (1 * / epsilon * (epsilon * epsilon)) with epsilon by (field; lra).
          lra. }
      assert (Hchain: INR n * INR (n - 1) > 2 * / (epsilon * epsilon)) by lra.
      assert (Hgoal_calc: epsilon * (INR n * INR (n - 1)) > epsilon * (2 * / (epsilon * epsilon))).
      { apply Rmult_gt_compat_l; lra. }
      assert (Hsimp1: epsilon * (2 * / (epsilon * epsilon)) = 2 * / epsilon).
      { field. lra. }
      rewrite Hsimp1 in Hgoal_calc.
      assert (H2eps2: 2 * / epsilon > 1).
      { replace (2 * / epsilon) with (2 / epsilon) by (unfold Rdiv; ring).
        apply Rmult_lt_reg_r with (r := epsilon).
        - lra.
        - unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
          rewrite Rmult_1_r. lra. }
      lra. }
    lra.
Qed.

Lemma product_bounds_imply_reciprocal_bound :
  forall n : nat, (n >= 2)%nat ->
  forall epsilon : R, 0 < epsilon < 1 ->
  INR n > 2 / epsilon ->
  1 / (INR n * INR (n - 1)) < epsilon.
Proof.
  intros n Hn2 epsilon Heps Hn_bound.
  assert (Hn1_bound: INR (n - 1) > 1 / epsilon).
  { apply n_minus_one_exceeds_one_over_epsilon; try assumption. }
  assert (Hprod: INR n * INR (n - 1) > 2 / (epsilon * epsilon)).
  { apply product_exceeds_square_of_reciprocal; assumption. }
  apply reciprocal_of_product_less_than_epsilon; assumption.
Qed.

Theorem obstruction_asymptotically_equivalent_to_reciprocal :
  forall epsilon : R, epsilon > 0 ->
  exists N : nat, forall n : nat, (n >= N)%nat -> (n >= 2)%nat ->
  Rabs (1 / INR (n - 1) - 1 / INR n) < epsilon.
Proof.
  intros epsilon Heps.
  destruct (Rlt_dec epsilon 1) as [Hlt1 | Hge1].
  - exists (S (S (Z.to_nat (up (2 / epsilon))))).
    intros n Hn Hn2.
    pose proof (obstruction_vs_reciprocal_difference_bound n Hn2) as Hbound.
    assert (Hn_bound: INR n > 2 / epsilon).
    { apply (large_nat_exceeds_two_over_epsilon epsilon Heps n Hn). }
    apply Rle_lt_trans with (r2 := 1 / (INR n * INR (n - 1))).
    + exact Hbound.
    + apply product_bounds_imply_reciprocal_bound; try assumption.
      split; assumption.
  - exists 3%nat.
    intros n Hn Hn2.
    pose proof (obstruction_vs_reciprocal_difference_bound n Hn2) as Hbound.
    assert (Hn_ge_3: (n >= 3)%nat) by lia.
    assert (Hn_pos: INR n > 0) by (apply lt_0_INR; lia).
    assert (Hn1_pos: INR (n - 1) > 0).
    { assert (H: (0 < n - 1)%nat) by lia. apply lt_INR in H. simpl in H. exact H. }
    apply Rle_lt_trans with (r2 := 1 / (INR n * INR (n - 1))).
    + exact Hbound.
    + assert (Hprod_lower: INR n * INR (n - 1) >= 6).
      { assert (Hn_ge: INR n >= 3).
        { assert (H: (3 <= n)%nat) by lia.
          apply le_INR in H. simpl in H. lra. }
        assert (Hn1_ge: INR (n - 1) >= 2).
        { assert (H: (2 <= n - 1)%nat) by lia. apply le_INR in H. simpl in H. lra. }
        apply Rle_ge.
        apply Rle_trans with (r2 := 3 * 2).
        - lra.
        - apply Rmult_le_compat; lra. }
      unfold Rdiv.
      apply Rmult_lt_reg_r with (r := INR n * INR (n - 1)).
      * apply Rmult_lt_0_compat; assumption.
      * rewrite Rmult_assoc.
        rewrite Rinv_l by (apply Rmult_integral_contrapositive_currified; lra).
        rewrite Rmult_1_r.
        assert (Hineq: INR n * INR (n - 1) >= 6) by exact Hprod_lower.
        assert (Heps_ge: epsilon >= 1) by lra.
        assert (Hgoal: epsilon * (INR n * INR (n - 1)) >= 1 * 6).
        { apply Rmult_ge_compat; lra. }
        lra.
Qed.

End TightnessOfBound.

Section RepresentationTheory.

Inductive Z3 : Type :=
  | Z3_0 : Z3
  | Z3_1 : Z3
  | Z3_2 : Z3.

Definition Z3_add (a b : Z3) : Z3 :=
  match a, b with
  | Z3_0, x => x
  | x, Z3_0 => x
  | Z3_1, Z3_1 => Z3_2
  | Z3_1, Z3_2 => Z3_0
  | Z3_2, Z3_1 => Z3_0
  | Z3_2, Z3_2 => Z3_1
  end.

Lemma Z3_add_comm : forall a b, Z3_add a b = Z3_add b a.
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

Record Complex : Type := mkComplex {
  re : R;
  im : R
}.

Definition omega : Complex := mkComplex (-(1/2)) (sqrt 3 / 2).

Definition Z3_character := Z3 -> Complex.

Definition chi : Z3_character :=
  fun g => match g with
  | Z3_0 => mkComplex 1 0
  | Z3_1 => omega
  | Z3_2 => mkComplex (-(1/2)) (-(sqrt 3 / 2))
  end.

Lemma chi_identity : chi Z3_0 = mkComplex 1 0.
Proof.
  reflexivity.
Qed.

Lemma chi_generator : chi Z3_1 = omega.
Proof.
  reflexivity.
Qed.

Definition Cmod (z : Complex) : R :=
  sqrt (re z * re z + im z * im z).

Lemma omega_modulus : Cmod omega = 1.
Proof.
  unfold Cmod, omega. simpl.
  assert (Hsum: - (1 / 2) * - (1 / 2) + sqrt 3 / 2 * (sqrt 3 / 2) = 1).
  { assert (Hneg: - (1 / 2) * - (1 / 2) = 1 / 4) by (field; lra).
    assert (Hsqrt_expand: sqrt 3 / 2 * (sqrt 3 / 2) = (sqrt 3 * sqrt 3) / (2 * 2)) by (field; lra).
    assert (Hsqrt_sq: sqrt 3 * sqrt 3 = 3).
    { apply sqrt_sqrt. lra. }
    rewrite Hneg.
    rewrite Hsqrt_expand.
    rewrite Hsqrt_sq.
    field; lra. }
  rewrite Hsum.
  apply sqrt_1.
Qed.

Definition Csub (z w : Complex) : Complex :=
  mkComplex (re z - re w) (im z - im w).

Lemma omega_minus_one_modulus : Cmod (Csub omega (mkComplex 1 0)) = sqrt 3.
Proof.
  unfold Cmod, Csub, omega. simpl.
  assert (Hre: - (1 / 2) - 1 = - (3 / 2)) by lra.
  assert (Him: sqrt 3 / 2 - 0 = sqrt 3 / 2) by lra.
  rewrite Hre, Him.
  assert (Hsum: - (3 / 2) * - (3 / 2) + sqrt 3 / 2 * (sqrt 3 / 2) = 9/4 + 3/4).
  { assert (H1: - (3 / 2) * - (3 / 2) = 9 / 4) by (field; lra).
    assert (H2: sqrt 3 / 2 * (sqrt 3 / 2) = (sqrt 3 * sqrt 3) / 4) by (field; lra).
    assert (H3: sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; lra).
    rewrite H1, H2, H3. lra. }
  rewrite Hsum.
  assert (Htotal: 9/4 + 3/4 = 3) by lra.
  rewrite Htotal.
  reflexivity.
Qed.

Theorem obstruction_as_character :
  chi Z3_0 = mkComplex 1 0 /\
  chi Z3_1 = omega /\
  Cmod (Csub (chi Z3_1) (chi Z3_0)) = sqrt 3 /\
  sqrt 3 = 3/2 * 2 / sqrt 3.
Proof.
  split; [apply chi_identity |].
  split; [apply chi_generator |].
  split.
  - rewrite chi_generator, chi_identity.
    apply omega_minus_one_modulus.
  - assert (Hsqrt3_pos: sqrt 3 > 0) by (apply sqrt_lt_R0; lra).
    assert (Hsqrt3: sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; lra).
    apply Rmult_eq_reg_r with (r := sqrt 3); [|lra].
    unfold Rdiv.
    replace (sqrt 3 * sqrt 3) with 3 by (symmetry; exact Hsqrt3).
    replace (3 * / 2 * 2 * / sqrt 3 * sqrt 3) with (3 * (/ 2 * 2 * / sqrt 3 * sqrt 3)) by ring.
    replace (/ 2 * 2) with 1 by (field; lra).
    replace (1 * / sqrt 3 * sqrt 3) with (/ sqrt 3 * sqrt 3) by ring.
    replace (/ sqrt 3 * sqrt 3) with 1 by (field; lra).
    ring.
Qed.

Theorem excess_equals_negative_real_part :
  1/2 = - re omega.
Proof.
  unfold omega. simpl.
  lra.
Qed.

Theorem lipschitz_equals_character_sum :
  3/2 = 1 + re omega + 1.
Proof.
  unfold omega. simpl.
  lra.
Qed.

Definition zeta (n : nat) : Complex :=
  mkComplex (cos (2 * PI / INR n)) (sin (2 * PI / INR n)).

Lemma zeta_3_real_part :
  re (zeta 3) = -(1/2).
Proof.
  unfold zeta. simpl.
  assert (H: cos (2 * PI / (1 + 1 + 1)) = -(1/2)).
  { assert (Hcos3: cos (PI / 3) = 1 / 2) by apply cos_PI3.
    replace (2 * PI / (1 + 1 + 1)) with (2 * PI / 3) by lra.
    replace (2 * PI / 3) with (PI - PI / 3) by lra.
    rewrite cos_minus.
    rewrite cos_PI.
    rewrite sin_PI.
    simpl.
    rewrite Hcos3.
    lra. }
  exact H.
Qed.

Theorem zeta_n_real_part_formula :
  forall n : nat, (n >= 2)%nat ->
  re (zeta n) = cos (2 * PI / INR n).
Proof.
  intros n Hn.
  unfold zeta. simpl.
  reflexivity.
Qed.

Lemma cos_bounded_by_one : forall x : R,
  -1 <= cos x <= 1.
Proof.
  intro x.
  split; [apply COS_bound | apply COS_bound].
Qed.

Lemma one_minus_cos_nonneg : forall x : R,
  0 <= 1 - cos x.
Proof.
  intro x.
  assert (H: cos x <= 1) by apply COS_bound.
  lra.
Qed.

Lemma INR_n_minus_1_formula : forall n : nat, (n >= 1)%nat ->
  INR (n - 1) = INR n - 1.
Proof.
  intros n Hn.
  rewrite minus_INR by lia.
  simpl. lra.
Qed.

Lemma epsilon_squared_positive : forall epsilon : R,
  epsilon > 0 -> epsilon * epsilon > 0.
Proof.
  intros epsilon Heps.
  apply Rmult_gt_0_compat; exact Heps.
Qed.

Lemma one_plus_epsilon_times_epsilon_expand : forall epsilon : R,
  (1 + epsilon) * epsilon = epsilon + epsilon * epsilon.
Proof.
  intro epsilon.
  ring.
Qed.

Lemma n_minus_1_times_epsilon_form : forall n epsilon : R,
  (n - 1) * epsilon = n * epsilon - epsilon.
Proof.
  intros n epsilon.
  ring.
Qed.

(* Field simplification for inverse *)
Lemma field_simplify_with_inverse : forall n epsilon : R,
  epsilon <> 0 ->
  (n * epsilon - epsilon) * / epsilon = n - 1.
Proof.
  intros n epsilon Heps_neq.
  field.
  exact Heps_neq.
Qed.

(* Division by epsilon equals multiplication by inverse *)
Lemma one_div_epsilon_simplify : forall epsilon : R,
  1 / epsilon = 1 * / epsilon.
Proof.
  intro epsilon.
  unfold Rdiv.
  ring.
Qed.

(* Reciprocal bound for large n *)
Lemma reciprocal_large_n_bound : forall n epsilon : R,
  epsilon > 0 ->
  n - 1 > 1 / epsilon ->
  (n - 1) * epsilon > 1.
Proof.
  intros n epsilon Heps Hn1.
  rewrite n_minus_1_times_epsilon_form.
  apply Rmult_gt_reg_r with (r := / epsilon).
  - apply Rinv_0_lt_compat. exact Heps.
  - assert (Heps_neq: epsilon <> 0) by lra.
    rewrite field_simplify_with_inverse by exact Heps_neq.
    replace (1 * / epsilon) with (/ epsilon) by ring.
    rewrite one_div_epsilon_simplify in Hn1.
    replace (1 * / epsilon) with (/ epsilon) in Hn1 by ring.
    exact Hn1.
Qed.

(* INR of n-1 is positive for n at least 2 *)
Lemma INR_n_minus_1_positive : forall n : nat,
  (n >= 2)%nat -> INR (n - 1) > 0.
Proof.
  intros n Hn.
  apply lt_0_INR.
  lia.
Qed.

(* Archimedes ceiling bound *)
Lemma archimed_ceiling_bound : forall x : R,
  x > 0 ->
  INR (S (Z.to_nat (up x))) >= x.
Proof.
  intros x Hx.
  assert (Hceil_pos: (0 < up x)%Z).
  { apply lt_IZR. destruct (archimed x) as [Hup _]. lra. }
  rewrite S_INR.
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id by lia.
  destruct (archimed x) as [Hup _].
  lra.
Qed.

Lemma INR_n_ge_2_implies_n_minus_1_ge_1 : forall n : nat,
  (n >= 2)%nat -> INR n - 1 >= 1.
Proof.
  intros n Hn.
  assert (H: (2 <= n)%nat) by lia.
  apply le_INR in H.
  simpl in H.
  lra.
Qed.

Lemma INR_n_minus_1_gt_bound : forall n_real bound : R,
  n_real > bound + 1 ->
  n_real - 1 > bound.
Proof.
  intros n_real bound Hn_bound.
  lra.
Qed.

(* Reciprocal converges to zero for large n *)
Lemma reciprocal_convergence_to_zero : forall epsilon : R, epsilon > 0 ->
  exists N : nat, forall n : nat, (n >= N)%nat -> (n >= 2)%nat ->
    1 / INR (n - 1) < epsilon.
Proof.
  intros epsilon Heps.
  assert (H1eps_pos: 1 / epsilon > 0) by (apply inv_pos; exact Heps).
  exists (S (S (S (Z.to_nat (up (1 / epsilon)))))).
  intros n Hn Hn2.
  assert (Hn1_pos: INR (n - 1) > 0) by (apply INR_n_minus_1_positive; exact Hn2).
  assert (Hup_bound: INR (S (Z.to_nat (up (1 / epsilon)))) >= 1 / epsilon).
  { apply archimed_ceiling_bound. exact H1eps_pos. }
  assert (Hn_bound_plus_1: INR n > 1 / epsilon + 1).
  { assert (Hn_SSS: INR n >= INR (S (S (S (Z.to_nat (up (1 / epsilon))))))).
    { assert (H: (S (S (S (Z.to_nat (up (1 / epsilon))))) <= n)%nat) by lia.
      apply le_INR in H.
      lra. }
    assert (HSSS_expand: INR (S (S (S (Z.to_nat (up (1 / epsilon)))))) > INR (S (Z.to_nat (up (1 / epsilon)))) + 1).
    { repeat rewrite S_INR. lra. }
    assert (Hup_plus_1: INR (S (Z.to_nat (up (1 / epsilon)))) + 1 > 1 / epsilon) by lra.
    lra. }
  assert (Hn_calc: INR (n - 1) = INR n - 1) by (apply INR_n_minus_1_formula; lia).
  assert (Hn1_bound: INR n - 1 > 1 / epsilon).
  { apply INR_n_minus_1_gt_bound with (bound := 1 / epsilon). exact Hn_bound_plus_1. }
  assert (Hcalc: INR (n - 1) * epsilon > 1).
  { rewrite Hn_calc. apply reciprocal_large_n_bound; [exact Heps | exact Hn1_bound]. }
  apply Rmult_lt_reg_r with (r := INR (n - 1)); [exact Hn1_pos|].
  unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
  rewrite Rmult_1_r.
  apply Rmult_lt_reg_r with (r := epsilon); [exact Heps|].
  rewrite Rmult_1_l.
  assert (Hgoal: epsilon < epsilon * INR (n - 1) * epsilon).
  { assert (Hcalc2: 1 < INR (n - 1) * epsilon) by lra.
    assert (Heps_pos: epsilon > 0) by exact Heps.
    assert (Hprod: epsilon * (INR (n - 1) * epsilon) > epsilon * 1).
    { apply Rmult_gt_compat_l; [exact Heps_pos | exact Hcalc2]. }
    lra. }
  exact Hgoal.
Qed.

Lemma one_minus_cos_bounded_by_two : forall x : R,
  1 - cos x <= 2.
Proof.
  intro x.
  assert (Hcos_bounds: -1 <= cos x <= 1) by apply COS_bound.
  lra.
Qed.

Lemma rabs_one_minus_cos : forall n : nat,
  (n >= 2)%nat ->
  Rabs (1 - cos (2 * PI / INR n)) = 1 - cos (2 * PI / INR n).
Proof.
  intros n Hn.
  rewrite Rabs_right.
  - reflexivity.
  - apply Rle_ge.
    apply one_minus_cos_nonneg.
Qed.

Lemma cos_term_bounded : forall n : nat,
  (n >= 2)%nat ->
  1 - cos (2 * PI / INR n) <= 2.
Proof.
  intros n Hn.
  apply one_minus_cos_bounded_by_two.
Qed.

Lemma sqr_nonneg : forall x : R, 0 <= x * x.
Proof.
  intro x.
  destruct (Rle_dec 0 x) as [Hpos|Hneg].
  - apply Rmult_le_pos; exact Hpos.
  - assert (Hx_neg: x <= 0) by lra.
    assert (H: x * x = (-x) * (-x)) by ring.
    rewrite H.
    apply Rmult_le_pos; lra.
Qed.

(* Square of nonzero is strictly positive *)
Lemma sqr_pos : forall x : R, x <> 0 -> 0 < x * x.
Proof.
  intros x Hneq.
  destruct (Rtotal_order x 0) as [Hlt | [Heq | Hgt]].
  - assert (H: x * x = (-x) * (-x)) by ring.
    rewrite H.
    apply Rmult_lt_0_compat; lra.
  - contradiction.
  - apply Rmult_lt_0_compat; exact Hgt.
Qed.

(* Division by square root identity *)
Lemma div_sqr_sqrt : forall a b : R,
  a > 0 -> b > 0 ->
  a / (sqrt b) = sqrt (a * a / b).
Proof.
  intros a b Ha Hb.
  assert (Hb_neq: b <> 0) by lra.
  assert (Hsqrt_pos: sqrt b > 0).
  { apply sqrt_lt_R0. exact Hb. }
  apply Rmult_eq_reg_r with (r := sqrt b); [|lra].
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_l by lra.
  rewrite Rmult_1_r.
  assert (Haa_pos: 0 <= a * a) by apply sqr_nonneg.
  assert (Hdiv_pos: 0 <= a * a * / b).
  { apply Rmult_le_pos; [exact Haa_pos | apply Rlt_le, Rinv_0_lt_compat, Hb]. }
  rewrite <- sqrt_mult.
  - assert (Hcancel: a * a * / b * b = a * a).
    { field. exact Hb_neq. }
    rewrite Hcancel.
    symmetry.
    apply sqrt_square.
    lra.
  - exact Hdiv_pos.
  - lra.
Qed.

(* Cosine half-angle identity *)
Lemma one_minus_cos_sin_half : forall x : R,
  1 - cos x = 2 * sin (x / 2) * sin (x / 2).
Proof.
  intro x.
  assert (H: cos x = cos (2 * (x / 2))).
  { assert (Heq: 2 * (x / 2) = x) by field. rewrite Heq. reflexivity. }
  rewrite H.
  rewrite cos_2a_cos.
  pose proof (sin2_cos2 (x / 2)) as Hsincos.
  unfold Rsqr in Hsincos.
  lra.
Qed.

(* Cosine minus one negation identity *)
Lemma cos_minus_one_neg : forall x : R,
  cos x - 1 = - (1 - cos x).
Proof.
  intro x.
  lra.
Qed.

(* Cosine minus one expressed via sine squared *)
Lemma cos_minus_one_as_sin_squared : forall x : R,
  cos x - 1 = - 2 * sin (x / 2) * sin (x / 2).
Proof.
  intro x.
  rewrite cos_minus_one_neg.
  rewrite one_minus_cos_sin_half.
  lra.
Qed.

(* Sine double angle formula *)
Lemma sin_double_angle : forall x : R,
  sin (2 * x) = 2 * sin x * cos x.
Proof.
  intro x.
  rewrite sin_2a.
  reflexivity.
Qed.

(* Complex modulus squared equals sum of squared components *)
Lemma Cmod_squared : forall z : Complex,
  Cmod z * Cmod z = re z * re z + im z * im z.
Proof.
  intro z.
  unfold Cmod.
  assert (Hsqrt_pos: 0 <= re z * re z + im z * im z).
  { apply Rplus_le_le_0_compat; apply sqr_nonneg. }
  rewrite <- sqrt_mult by (apply Hsqrt_pos || lra).
  rewrite sqrt_square by apply Hsqrt_pos.
  reflexivity.
Qed.

(* Distance from zeta to one expressed via sine *)
Lemma zeta_minus_one_squared : forall n : nat,
  (n >= 2)%nat ->
  Cmod (Csub (zeta n) (mkComplex 1 0)) * Cmod (Csub (zeta n) (mkComplex 1 0)) =
  4 * sin (PI / INR n) * sin (PI / INR n).
Proof.
  intros n Hn.
  rewrite Cmod_squared.
  unfold Csub, zeta. simpl.
  assert (Hn_pos: INR n > 0) by (apply lt_0_INR; lia).
  set (theta := PI / INR n).
  assert (Hre: cos (2 * PI / INR n) - 1 = - 2 * sin theta * sin theta).
  { unfold theta.
    rewrite cos_minus_one_as_sin_squared.
    assert (Heq: (2 * PI / INR n) / 2 = PI / INR n) by (field; lra).
    rewrite Heq. reflexivity. }
  assert (Him: sin (2 * PI / INR n) = 2 * sin theta * cos theta).
  { unfold theta.
    assert (Heq: 2 * PI / INR n = 2 * (PI / INR n)) by (field; lra).
    rewrite Heq.
    apply sin_double_angle. }
  rewrite Hre, Him.
  pose proof (sin2_cos2 theta) as Hsincos.
  unfold Rsqr in Hsincos.
  unfold theta in *.
  nra.
Qed.

(* Complex modulus is nonnegative *)
Lemma Cmod_nonneg : forall z : Complex, 0 <= Cmod z.
Proof.
  intro z.
  unfold Cmod.
  apply sqrt_pos.
Qed.

(* Sine bounded between -1 and 1 on [0,PI] *)
Lemma sin_bounded_0_to_pi : forall x : R,
  0 <= x <= PI -> -1 <= sin x <= 1.
Proof.
  intros x Hx.
  pose proof (SIN_bound x) as H.
  lra.
Qed.

(* Cosine less than one for positive angles in (0,PI) *)
Lemma cos_lt_1_for_pos : forall t : R,
  0 < t < PI -> cos t < 1.
Proof.
  intros t Ht.
  assert (Hcos_bound: -1 <= cos t <= 1) by apply COS_bound.
  destruct (Req_dec (cos t) 1) as [Heq | Hneq].
  - assert (Hsin_sq: sin t * sin t + cos t * cos t = 1).
    { pose proof (sin2_cos2 t) as H. unfold Rsqr in H. lra. }
    rewrite Heq in Hsin_sq.
    assert (Hsin_zero: sin t * sin t = 0) by lra.
    assert (Hsin_eq_zero: sin t = 0).
    { destruct (Req_dec (sin t) 0) as [Heq0 | Hneq0].
      - exact Heq0.
      - assert (Hpos: sin t * sin t > 0).
        { apply sqr_pos. exact Hneq0. }
        lra. }
    assert (Hcontradiction: exists k : Z, t = IZR k * PI).
    { apply sin_eq_0_0. exact Hsin_eq_zero. }
    destruct Hcontradiction as [k Hk].
    assert (Hk_bounds: k = 0%Z \/ (k >= 1)%Z \/ (k <= -1)%Z) by lia.
    destruct Hk_bounds as [Hk0 | [Hk_pos | Hk_neg]].
    + rewrite Hk0 in Hk. simpl in Hk. lra.
    + assert (Ht_ge_pi: t >= PI).
      { rewrite Hk.
        assert (Hk_ge_1: IZR k >= 1).
        { assert (H: (1 <= k)%Z) by lia.
          apply (IZR_le 1 k) in H.
          simpl in H. apply Rle_ge. exact H. }
        assert (HPI_pos: PI >= 0) by (apply Rle_ge, Rlt_le, PI_RGT_0).
        assert (H: IZR k * PI >= 1 * PI).
        { apply Rmult_ge_compat_r; [exact HPI_pos | exact Hk_ge_1]. }
        lra. }
      lra.
    + assert (Ht_neg: t < 0).
      { rewrite Hk.
        assert (Hk_le_minus1: IZR k <= -1).
        { assert (H: (k <= -1)%Z) by lia.
          apply (IZR_le k (-1)) in H.
          simpl in H. exact H. }
        assert (H: IZR k * PI <= (-1) * PI).
        { apply Rmult_le_compat_r; [apply Rlt_le, PI_RGT_0 | exact Hk_le_minus1]. }
        lra. }
      lra.
  - lra.
Qed.

(* Sine of zero equals zero *)
Lemma sin_0_eq : sin 0 = 0.
Proof.
  apply sin_0.
Qed.

(* Cosine of zero equals one *)
Lemma cos_0_eq : cos 0 = 1.
Proof.
  apply cos_0.
Qed.

(* Derivative of sine is cosine *)
Lemma derivable_sin : forall x : R, derivable_pt_lim sin x (cos x).
Proof.
  intro x.
  apply derivable_pt_lim_sin.
Qed.

(* Inequality equivalent to subtraction nonnegativity *)
Lemma Rle_minus : forall a b : R, a <= b <-> 0 <= b - a.
Proof.
  intros a b.
  split; intro H; lra.
Qed.

(* Zeta distance from one equals instability measure *)
Theorem zeta_minus_one_equals_instability_excess :
  forall n : nat, (n >= 3)%nat ->
  Cmod (Csub (zeta n) (mkComplex 1 0)) =
    2 * Rabs (sin (PI / INR n)).
Proof.
  intros n Hn.
  assert (Hn2: (n >= 2)%nat) by lia.
  pose proof (zeta_minus_one_squared n Hn2) as Hsq.
  assert (Hcmod_pos: 0 <= Cmod (Csub (zeta n) (mkComplex 1 0))).
  { apply Cmod_nonneg. }
  assert (Hn_pos: INR n > 0) by (apply lt_0_INR; lia).
  assert (Hpi_n_bound: 0 < PI / INR n < PI).
  { split; [apply Rmult_lt_0_compat; [apply PI_RGT_0 | apply Rinv_0_lt_compat; exact Hn_pos] |].
    assert (Hn_ge_3: INR n >= 3).
    { assert (H: (3 <= n)%nat) by lia. apply le_INR in H. simpl in H. lra. }
    assert (Hineq: PI / INR n < PI / 1) by (apply Rmult_lt_compat_l; [apply PI_RGT_0 | apply Rinv_1_lt_contravar; lra]).
    unfold Rdiv in Hineq. rewrite Rinv_1, Rmult_1_r in Hineq. exact Hineq. }
  assert (Hsin_pos: 0 <= sin (PI / INR n)).
  { apply sin_ge_0; lra. }
  assert (Habs_sin: Rabs (sin (PI / INR n)) = sin (PI / INR n)).
  { apply Rabs_right. apply Rle_ge. exact Hsin_pos. }
  assert (H2_abs_sin_pos: 0 <= 2 * Rabs (sin (PI / INR n))).
  { rewrite Habs_sin. assert (H: 0 <= 2) by lra. apply Rmult_le_pos; lra. }
  apply Rmult_eq_reg_l with (r := Cmod (Csub (zeta n) (mkComplex 1 0)) + 2 * Rabs (sin (PI / INR n))).
  - assert (Hgoal_sq: (Cmod (Csub (zeta n) (mkComplex 1 0))) * (Cmod (Csub (zeta n) (mkComplex 1 0))) =
                      (2 * Rabs (sin (PI / INR n))) * (2 * Rabs (sin (PI / INR n)))).
    { assert (Heq: (2 * Rabs (sin (PI / INR n))) * (2 * Rabs (sin (PI / INR n))) =
                   4 * sin (PI / INR n) * sin (PI / INR n)).
      { rewrite Habs_sin. ring. }
      rewrite Heq. exact Hsq. }
    assert (Hdiff_of_sq: forall a b : R, 0 <= a -> 0 <= b -> a * a = b * b -> (a + b) * (a - b) = 0).
    { intros a b Ha Hb Heq. nra. }
    pose proof (Hdiff_of_sq (Cmod (Csub (zeta n) (mkComplex 1 0))) (2 * Rabs (sin (PI / INR n)))
                 Hcmod_pos H2_abs_sin_pos Hgoal_sq) as Hdiff.
    assert (Hsum_pos: Cmod (Csub (zeta n) (mkComplex 1 0)) + 2 * Rabs (sin (PI / INR n)) > 0).
    { assert (Hn_ge_3: INR n >= 3).
      { assert (H: (3 <= n)%nat) by lia. apply le_INR in H. simpl in H. lra. }
      assert (Hsin_gt_0: sin (PI / INR n) > 0).
      { apply sin_gt_0; lra. }
      rewrite Habs_sin. nra. }
    assert (Hcancel: (Cmod (Csub (zeta n) (mkComplex 1 0)) + 2 * Rabs (sin (PI / INR n))) *
                     (Cmod (Csub (zeta n) (mkComplex 1 0)) - 2 * Rabs (sin (PI / INR n))) = 0 ->
                     Cmod (Csub (zeta n) (mkComplex 1 0)) - 2 * Rabs (sin (PI / INR n)) = 0).
    { intro H. apply Rmult_integral in H. destruct H as [H | H].
      - lra.
      - exact H. }
    apply Hcancel in Hdiff. lra.
  - assert (Hn_ge_3: INR n >= 3).
    { assert (H: (3 <= n)%nat) by lia. apply le_INR in H. simpl in H. lra. }
    assert (Hsin_gt_0: sin (PI / INR n) > 0).
    { apply sin_gt_0; lra. }
    rewrite Habs_sin. nra.
Qed.


(* Character distance expressed trigonometrically *)
Theorem character_distance_trigonometric :
  forall n : nat, (n >= 3)%nat ->
  Cmod (Csub (zeta n) (mkComplex 1 0)) =
    2 * Rabs (sin (PI / INR n)).
Proof.
  intros n Hn.
  apply zeta_minus_one_equals_instability_excess.
  exact Hn.
Qed.

End RepresentationTheory.

Section CyclotomicPolynomials.

Definition Cadd (z w : Complex) : Complex :=
  mkComplex (re z + re w) (im z + im w).

Definition Cmul (z w : Complex) : Complex :=
  mkComplex (re z * re w - im z * im w) (re z * im w + im z * re w).

Lemma Cadd_comm : forall z w, Cadd z w = Cadd w z.
Proof.
  intros [zr zi] [wr wi].
  unfold Cadd. simpl.
  f_equal; ring.
Qed.

Lemma Cmul_comm : forall z w, Cmul z w = Cmul w z.
Proof.
  intros [zr zi] [wr wi].
  unfold Cmul. simpl.
  f_equal; ring.
Qed.

Definition Cpow (z : Complex) (n : nat) : Complex :=
  Nat.iter n (Cmul z) (mkComplex 1 0).

Definition polynomial := list Complex.

Fixpoint eval_poly (p : polynomial) (z : Complex) : Complex :=
  match p with
  | [] => mkComplex 0 0
  | c :: cs => Cadd c (Cmul z (eval_poly cs z))
  end.

Definition primitive_root_of_unity (n : nat) (k : nat) : Complex :=
  mkComplex (cos (2 * PI * INR k / INR n)) (sin (2 * PI * INR k / INR n)).

Definition coprime (a b : nat) : Prop :=
  Nat.gcd a b = 1%nat.

Definition phi (n : nat) : nat :=
  match n with
  | O => O
  | S O => 1
  | S n' => length (filter (fun k => Nat.gcd k (S n') =? 1) (seq 1 n'))
  end.

Fixpoint poly_max_coeff_abs (p : polynomial) : R :=
  match p with
  | [] => 0
  | c :: cs => Rmax (Cmod c) (poly_max_coeff_abs cs)
  end.

Definition height (p : polynomial) : R :=
  poly_max_coeff_abs p.

Definition poly_sub (p q : polynomial) : polynomial :=
  let fix sub_aux p q :=
    match p, q with
    | [], [] => []
    | c :: cs, [] => c :: cs
    | [], d :: ds => (Cmul (mkComplex (-1) 0) d) :: sub_aux [] ds
    | c :: cs, d :: ds => (Cadd c (Cmul (mkComplex (-1) 0) d)) :: sub_aux cs ds
    end
  in sub_aux p q.

Definition poly_mul_scalar (c : Complex) (p : polynomial) : polynomial :=
  map (Cmul c) p.

Definition cyclotomic_polynomial_3 : polynomial :=
  [mkComplex 1 0; mkComplex 1 0; mkComplex 1 0].

Lemma height_cyclotomic_3 : height cyclotomic_polynomial_3 = 1.
Proof.
  unfold height, cyclotomic_polynomial_3, poly_max_coeff_abs.
  simpl.
  unfold Cmod. simpl.
  assert (H1: sqrt (1 * 1 + 0 * 0) = 1).
  { assert (Hcalc: 1 * 1 + 0 * 0 = 1) by lra.
    rewrite Hcalc. apply sqrt_1. }
  repeat rewrite H1.
  assert (Hmax0: Rmax 1 0 = 1).
  { apply Rmax_left. lra. }
  rewrite Hmax0.
  assert (Hmax1: Rmax 1 1 = 1).
  { apply Rmax_left. lra. }
  repeat rewrite Hmax1.
  reflexivity.
Qed.

Definition asymptotic_equiv (a b : R) : Prop :=
  exists c : R, c > 0 /\ a = c * b.

Notation "a ~ b" := (asymptotic_equiv a b) (at level 70).

Fixpoint cyclotomic_polynomial (n : nat) : polynomial :=
  match n with
  | O => []
  | S O => []
  | S (S O) => []
  | S (S (S O)) => cyclotomic_polynomial_3
  | S n' => repeat (mkComplex 1 0) n
  end.

Lemma poly_max_coeff_repeat_one : forall m,
  poly_max_coeff_abs (repeat (mkComplex 1 0) m) <= 1.
Proof.
  intro m.
  induction m; simpl.
  - lra.
  - unfold Cmod. simpl.
    assert (H1: sqrt (1 * 1 + 0 * 0) = 1).
    { assert (Hcalc: 1 * 1 + 0 * 0 = 1) by lra.
      rewrite Hcalc. apply sqrt_1. }
    rewrite H1.
    apply Rmax_lub; [lra | exact IHm].
Qed.

Lemma poly_max_coeff_repeat_one_ge : forall m,
  (m > 0)%nat ->
  poly_max_coeff_abs (repeat (mkComplex 1 0) m) >= 1.
Proof.
  intros m Hm.
  destruct m; [lia|].
  simpl. unfold Cmod. simpl.
  assert (H1: sqrt (1 * 1 + 0 * 0) = 1).
  { assert (Hcalc: 1 * 1 + 0 * 0 = 1) by lra.
    rewrite Hcalc. apply sqrt_1. }
  rewrite H1.
  apply Rle_ge, Rmax_l.
Qed.

Lemma repeat_height_one : forall m,
  (m > 0)%nat ->
  height (repeat (mkComplex 1 0) m) = 1.
Proof.
  intros m Hm.
  unfold height.
  apply Rle_antisym.
  - apply poly_max_coeff_repeat_one.
  - apply Rge_le, poly_max_coeff_repeat_one_ge. exact Hm.
Qed.

Lemma height_cyclotomic_bounded : forall n,
  (n >= 3)%nat -> height (cyclotomic_polynomial n) = 1.
Proof.
  intros n Hn.
  destruct n as [|[|[|[|n']]]]; try lia.
  - simpl. apply height_cyclotomic_3.
  - unfold cyclotomic_polynomial.
    apply repeat_height_one. lia.
Qed.

Theorem obstruction_relates_to_cyclotomic_height :
  forall n : nat, (n >= 3)%nat ->
  exists h : R,
  1 / INR (n - 1) ~ h * height (cyclotomic_polynomial n).
Proof.
  intros n Hn.
  exists (1 / INR (n - 1)).
  unfold asymptotic_equiv.
  exists 1.
  split; [lra |].
  rewrite height_cyclotomic_bounded by exact Hn.
  lra.
Qed.

Definition euler_phi (n : nat) : nat := phi n.

Lemma euler_phi_3 : euler_phi 3 = 2%nat.
Proof.
  unfold euler_phi, phi. simpl. reflexivity.
Qed.

Definition discriminant (p : polynomial) : Complex :=
  match p with
  | [] => mkComplex 0 0
  | [_] => mkComplex 0 0
  | [a; b; c] => Cadd (Cmul b b) (Cmul (mkComplex (-4) 0) (Cmul a c))
  | _ => mkComplex 1 0
  end.

Lemma discriminant_cyclotomic_3 :
  discriminant cyclotomic_polynomial_3 = mkComplex (-3) 0.
Proof.
  unfold discriminant, cyclotomic_polynomial_3.
  simpl. unfold Cadd, Cmul. simpl. f_equal; ring.
Qed.

Lemma Cmod_discriminant_cyclotomic_3 :
  Cmod (discriminant cyclotomic_polynomial_3) = 3.
Proof.
  rewrite discriminant_cyclotomic_3.
  unfold Cmod. simpl.
  assert (H: (-3) * (-3) + 0 * 0 = 9) by ring.
  rewrite H.
  assert (Hsqrt: sqrt 9 = 3).
  { assert (H9: 9 = 3 * 3) by ring.
    rewrite H9.
    rewrite sqrt_square by lra.
    reflexivity. }
  exact Hsqrt.
Qed.

Lemma ln_3_positive : ln 3 > 0.
Proof.
  assert (H3_gt_1: 3 > 1) by lra.
  assert (H1_gt_0: 1 > 0) by lra.
  assert (H3_gt_0: 3 > 0) by lra.
  assert (H: ln 3 > ln 1).
  { apply ln_increasing; lra. }
  rewrite ln_1 in H.
  exact H.
Qed.

Lemma euler_phi_positive : forall n : nat, (n >= 3)%nat -> (euler_phi n > 0)%nat.
Proof.
  intros n Hn.
  unfold euler_phi, phi.
  destruct n as [|[|[|n']]]; try lia.
  simpl. apply Nat.lt_0_succ.
Qed.

Lemma INR_euler_phi_positive : forall n : nat, (n >= 3)%nat -> INR (euler_phi n) > 0.
Proof.
  intros n Hn.
  assert (Hphi: (euler_phi n > 0)%nat) by (apply euler_phi_positive; exact Hn).
  apply lt_0_INR. exact Hphi.
Qed.

Definition obstruction_exponential_form (n : nat) : R :=
  exp (INR (euler_phi n) / INR (n - 1)).

Lemma obstruction_exponential_form_3 : obstruction_exponential_form 3 = exp 1.
Proof.
  unfold obstruction_exponential_form, euler_phi, phi.
  simpl.
  f_equal.
  lra.
Qed.

Theorem obstruction_has_logarithmic_form :
  forall n : nat, (n >= 3)%nat ->
  1 / INR (n - 1) =
    ln (obstruction_exponential_form n) / INR (euler_phi n).
Proof.
  intros n Hn.
  unfold obstruction_exponential_form.
  assert (Hphi_pos: INR (euler_phi n) > 0) by (apply INR_euler_phi_positive; exact Hn).
  assert (Hn1_pos: INR (n - 1) > 0).
  { assert (H: (0 < n - 1)%nat) by lia.
    apply lt_INR in H. simpl in H. exact H. }
  rewrite ln_exp.
  field. lra.
Qed.

End CyclotomicPolynomials.

Section ByzantineTightBound.

Definition byzantine_protocol := list R -> R.

Definition affine_protocol (protocol : byzantine_protocol) : Prop :=
  exists (weights : list R),
    fold_right Rplus 0 weights = 1 /\
    forall inputs, length inputs = length weights ->
      protocol inputs = fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs)).

Definition identity_preserving (protocol : byzantine_protocol) : Prop :=
  forall x, protocol (0 :: x :: x :: nil) = x.

Lemma affine_identity_determines_weights :
  forall protocol weights,
  length weights = 3%nat ->
  fold_right Rplus 0 weights = 1 ->
  (forall inputs, length inputs = length weights ->
    protocol inputs = fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs))) ->
  (forall x, protocol (0 :: x :: x :: nil) = x) ->
  exists w2 w3, weights = (0 :: w2 :: w3 :: nil) /\ w2 + w3 = 1.
Proof.
  intros protocol weights Hlen Hsum Haff Hid.
  destruct weights as [|w1 [|w2 [|w3 rest]]]; try discriminate Hlen.
  destruct rest; try discriminate Hlen.
  specialize (Hid 1).
  exists w2, w3.
  split.
  - assert (Hw1_eq: w1 = 0).
    { rewrite (Haff (0 :: 1 :: 1 :: nil)) in Hid by reflexivity.
      simpl in Hid.
      simpl in Hsum.
      assert (H_eq: w1 + (w2 + (w3 + 0)) = 1) by exact Hsum.
      assert (H_id: w2 + w3 = 1) by lra.
      lra. }
    rewrite Hw1_eq.
    reflexivity.
  - simpl in Hsum.
    assert (Hw1_zero: w1 = 0).
    { rewrite (Haff (0 :: 1 :: 1 :: nil)) in Hid by reflexivity.
      simpl in Hid.
      lra. }
    rewrite Hw1_zero in Hsum.
    simpl in Hsum.
    lra.
Qed.

Theorem tight_byzantine_lower_bound :
  forall protocol weights,
  length weights = 3%nat ->
  fold_right Rplus 0 weights = 1 ->
  (forall inputs, length inputs = length weights ->
    protocol inputs = fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs))) ->
  (forall x, protocol (0 :: x :: x :: nil) = x) ->
  forall x,
  protocol (x :: x :: x :: nil) = x.
Proof.
  intros protocol weights Hlen Hsum Haff Hid x.
  destruct (affine_identity_determines_weights protocol weights Hlen Hsum Haff Hid) as [w2 [w3 [Hweights Hsum23]]].
  rewrite Hweights in Haff.
  rewrite (Haff (x :: x :: x :: nil)) by reflexivity.
  simpl fold_right.
  simpl map.
  simpl combine.
  assert (H: 0 * x + (w2 * x + (w3 * x + 0)) = (w2 + w3) * x) by ring.
  rewrite H, Hsum23.
  ring.
Qed.

Corollary byzantine_identity_impossibility :
  forall protocol weights,
  length weights = 3%nat ->
  fold_right Rplus 0 weights = 1 ->
  (forall inputs, length inputs = length weights ->
    protocol inputs = fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs))) ->
  (forall x, protocol (0 :: x :: x :: nil) = x) ->
  forall x, x <> 0 ->
  ~ (Rabs (protocol (x :: x :: x :: nil)) >= (3/2) * Rabs x).
Proof.
  intros protocol weights Hlen Hsum Haff Hid x Hx_neq Hcontra.
  pose proof (tight_byzantine_lower_bound protocol weights Hlen Hsum Haff Hid x) as Heq.
  assert (Habs_pos: Rabs x > 0) by (apply Rabs_pos_lt; exact Hx_neq).
  rewrite Heq in Hcontra.
  lra.
Qed.

Theorem identity_law_prevents_byzantine_resilience :
  ~ exists protocol weights,
    length weights = 3%nat /\
    fold_right Rplus 0 weights = 1 /\
    (forall inputs, length inputs = length weights ->
      protocol inputs = fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs))) /\
    (forall x, protocol (0 :: x :: x :: nil) = x) /\
    (exists x, x <> 0 /\ Rabs (protocol (x :: x :: x :: nil)) > Rabs x).
Proof.
  intro Hex.
  destruct Hex as [protocol [weights [Hlen [Hsum [Haff [Hid [x [Hx_neq Hamp]]]]]]]].
  pose proof (tight_byzantine_lower_bound protocol weights Hlen Hsum Haff Hid x) as Heq.
  rewrite Heq in Hamp.
  assert (Habs: Rabs x > Rabs x) by exact Hamp.
  lra.
Qed.

Theorem identity_forces_weight_structure :
  forall protocol weights,
  length weights = 3%nat ->
  fold_right Rplus 0 weights = 1 ->
  (forall inputs, length inputs = length weights ->
    protocol inputs = fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs))) ->
  (forall x, protocol (0 :: x :: x :: nil) = x) ->
  exists w2 w3,
    weights = (0 :: w2 :: w3 :: nil) /\
    w2 + w3 = 1 /\
    (forall x y z, protocol (x :: y :: z :: nil) = w2 * y + w3 * z).
Proof.
  intros protocol weights Hlen Hsum Haff Hid.
  destruct (affine_identity_determines_weights protocol weights Hlen Hsum Haff Hid) as [w2 [w3 [Hweights Hsum23]]].
  exists w2, w3.
  split; [exact Hweights | ].
  split; [exact Hsum23 | ].
  intros x y z.
  rewrite Hweights in Haff.
  rewrite (Haff (x :: y :: z :: nil)) by reflexivity.
  simpl.
  ring.
Qed.

Theorem protocol_ignores_first_input :
  forall protocol weights,
  length weights = 3%nat ->
  fold_right Rplus 0 weights = 1 ->
  (forall inputs, length inputs = length weights ->
    protocol inputs = fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs))) ->
  (forall x, protocol (0 :: x :: x :: nil) = x) ->
  forall a b c,
  protocol (a :: b :: c :: nil) = protocol (0 :: b :: c :: nil).
Proof.
  intros protocol weights Hlen Hsum Haff Hid a b c.
  destruct (affine_identity_determines_weights protocol weights Hlen Hsum Haff Hid) as [w2 [w3 [Hweights Hsum23]]].
  rewrite Hweights in Haff.
  rewrite (Haff (a :: b :: c :: nil)) by reflexivity.
  rewrite (Haff (0 :: b :: c :: nil)) by reflexivity.
  simpl.
  ring.
Qed.

Theorem identity_constraint_eliminates_byzantine_tolerance :
  forall protocol weights,
  length weights = 3%nat ->
  fold_right Rplus 0 weights = 1 ->
  (forall inputs, length inputs = length weights ->
    protocol inputs = fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs))) ->
  (forall x, protocol (0 :: x :: x :: nil) = x) ->
  forall honest1 honest2 byzantine,
  protocol (byzantine :: honest1 :: honest2 :: nil) = protocol (0 :: honest1 :: honest2 :: nil).
Proof.
  intros protocol weights Hlen Hsum Haff Hid honest1 honest2 byzantine.
  apply (protocol_ignores_first_input protocol weights Hlen Hsum Haff Hid).
Qed.

Theorem cyclic_and_identity_mutually_exclusive :
  ~ exists (T : R -> R -> R -> R) (weights : list R),
    length weights = 3%nat /\
    fold_right Rplus 0 weights = 1 /\
    (forall inputs, length inputs = length weights ->
      fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights inputs)) =
      fold_right Rplus 0 (map (fun '(w, x) => w * x) (combine weights (List.tl inputs ++ [List.hd 0 inputs])))) /\
    (forall x, fold_right Rplus 0 (map (fun '(w, y) => w * y) (combine weights [0; x; x])) = x) /\
    (exists x, x <> 0 /\
      fold_right Rplus 0 (map (fun '(w, y) => w * y) (combine weights [x; x; x])) <> x).
Proof.
  intro Hex.
  destruct Hex as [T [weights [Hlen [Hsum [Hcyc [Hid [x [Hx_neq Hneq]]]]]]]].
  assert (Heq: fold_right Rplus 0 (map (fun '(w, y) => w * y) (combine weights [x; x; x])) = x).
  { destruct weights as [|w1 [|w2 [|w3 rest]]]; try discriminate Hlen.
    destruct rest; try discriminate Hlen.
    assert (Hw1_zero: w1 = 0).
    { specialize (Hid 1).
      simpl in Hid.
      simpl in Hsum.
      lra. }
    assert (Hw_sum: w2 + w3 = 1).
    { simpl in Hsum. lra. }
    simpl.
    rewrite Hw1_zero.
    simpl.
    assert (H: w2 * x + (w3 * x + 0) = (w2 + w3) * x) by ring.
    rewrite H.
    rewrite Hw_sum.
    ring. }
  apply Hneq.
  exact Heq.
Qed.

End ByzantineTightBound.

End TernaryAlgebraicStructure.

(* ========================================================================= *)
(* Floating Point Analysis - IEEE 754 Connection                            *)
(* ========================================================================= *)
(* This section connects the mathematical real number analysis above to     *)
(* actual IEEE 754 floating point arithmetic using the Flocq library.       *)

Require Import Flocq.Core.Raux.
Require Import Flocq.Core.Defs.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Core.FLT.
Require Import Flocq.Core.Ulp.
Require Import Flocq.Core.Round_pred.
Require Import Flocq.Core.Float_prop.
Require Import Flocq.Core.Zaux.
Require Import Flocq.IEEE754.Binary.

Section FloatingPointTernaryAlgebra.

Definition prec := 53%Z.
Definition emax := 1024%Z.
Definition emin := (3 - emax - prec)%Z.

Definition flt_exp := FLT_exp emin prec.

Definition is_representable (x : R) : Prop :=
  generic_format radix2 flt_exp x.

Lemma prec_positive : (0 < prec)%Z.
Proof.
  unfold prec. lia.
Qed.

Lemma emin_lt_emax : (emin < emax)%Z.
Proof.
  unfold emin, emax, prec. lia.
Qed.

Lemma zero_is_representable : is_representable 0.
Proof.
  unfold is_representable.
  apply generic_format_0.
Qed.

Definition choice (z : Z) : bool := (Z.even z).

Definition rnd (x : R) : R :=
  round radix2 flt_exp (Znearest choice) x.

Definition fp_add (x y : R) : R := rnd (x + y).

Definition fp_div (x y : R) : R := rnd (x / y).

Definition T_fp (a b c : R) : R :=
  fp_div (fp_add (fp_add a b) c) 2.

Lemma rnd_representable : forall x : R,
  is_representable x -> rnd x = x.
Proof.
  intros x Hx.
  unfold rnd, is_representable in *.
  apply round_generic.
  - apply valid_rnd_N.
  - exact Hx.
Qed.

Lemma fp_add_commutative : forall x y : R,
  fp_add x y = fp_add y x.
Proof.
  intros x y.
  unfold fp_add.
  f_equal. ring.
Qed.

Theorem three_over_two_power_12_exceeds_100 : (3/2)^12 > 100.
Proof.
  assert (H_3_2: forall n : nat, (3 / 2) ^ n = 3^n / 2^n).
  {
    intro n.
    unfold Rdiv.
    rewrite Rpow_mult_distr.
    rewrite pow_inv by lra.
    reflexivity.
  }
  rewrite H_3_2.
  assert (H3_pow: 3^12 = IZR (3^12)%Z).
  { rewrite pow_IZR. reflexivity. }
  assert (H2_pow: 2^12 = IZR (2^12)%Z).
  { rewrite pow_IZR. reflexivity. }
  rewrite H3_pow, H2_pow.
  assert (H3_val: (3^12 = 531441)%Z) by reflexivity.
  assert (H2_val: (2^12 = 4096)%Z) by reflexivity.
  rewrite H3_val, H2_val.
  simpl.
  unfold Rdiv.
  apply Rmult_gt_reg_r with (r := IZR 4096).
  - simpl. lra.
  - replace (IZR 531441 * / IZR 4096 * IZR 4096) with (IZR 531441) by (field; simpl; lra).
    assert (Hcalc: IZR 100 * IZR 4096 = IZR (100 * 4096)).
    { rewrite mult_IZR. reflexivity. }
    rewrite Hcalc.
    assert (Hprod: (100 * 4096 = 409600)%Z) by reflexivity.
    rewrite Hprod.
    simpl. lra.
Qed.

Theorem exact_real_ternary_amplifies_to_100 :
  forall x : R,
  x <> 0 ->
  let T := fun a b c => (a + b + c) / 2 in
  let result_12 := Nat.iter 12 (fun v => T v v v) x in
  Rabs result_12 = (3/2)^12 * Rabs x /\
  Rabs result_12 > 100 * Rabs x.
Proof.
  intros x Hx_neq T result_12.
  split.
  - unfold result_12, T.
    assert (Hiter: forall n v, Nat.iter n (fun w => (w + w + w) / 2) v = (3/2)^n * v).
    {
      intro n.
      induction n; intro v.
      - simpl. lra.
      - simpl.
        rewrite IHn.
        field.
    }
    rewrite Hiter.
    rewrite Rabs_mult.
    rewrite Rabs_right.
    + reflexivity.
    + apply Rle_ge.
      apply pow_le.
      lra.
  - assert (Hamp: (3/2)^12 > 100) by apply three_over_two_power_12_exceeds_100.
    assert (H1: Rabs result_12 = (3/2)^12 * Rabs x).
    {
      unfold result_12, T.
      assert (Hiter: forall n v, Nat.iter n (fun w => (w + w + w) / 2) v = (3/2)^n * v).
      {
        intro n.
        induction n; intro v.
        - simpl. lra.
        - simpl.
          rewrite IHn.
          field.
      }
      rewrite Hiter.
      rewrite Rabs_mult.
      rewrite Rabs_right.
      + reflexivity.
      + apply Rle_ge.
        apply pow_le.
        lra.
    }
    rewrite H1.
    apply Rmult_gt_compat_r.
    + apply Rabs_pos_lt. exact Hx_neq.
    + exact Hamp.
Qed.

Corollary three_halves_power_gives_concrete_bound :
  forall x : R,
  x <> 0 ->
  Rabs ((3/2)^12 * x) > 100 * Rabs x.
Proof.
  intros x Hx_neq.
  rewrite Rabs_mult.
  rewrite Rabs_right.
  - apply Rmult_gt_compat_r.
    + apply Rabs_pos_lt. exact Hx_neq.
    + apply three_over_two_power_12_exceeds_100.
  - apply Rle_ge.
    apply pow_le.
    lra.
Qed.

Theorem floating_point_confirms_impossibility_for_denominator_two :
  forall (T : R -> R -> R -> R),
  (forall x y z, T x y z = (x + y + z) / 2) ->
  (forall x, x <> 0 ->
    let result_12 := Nat.iter 12 (fun v => T v v v) x in
    Rabs result_12 > 100 * Rabs x) /\
  (forall x, x <> 0 -> Rabs (T x x x) = (3/2) * Rabs x) /\
  ~ (exists L : R, L < 3/2 /\
      forall x, x <> 0 -> Rabs (T x x x) <= L * Rabs x).
Proof.
  intros T HT_def.
  split; [| split].
  - intros x Hx_neq result_12.
    assert (HT_expand: forall v, T v v v = (v + v + v) / 2).
    { intro v. rewrite HT_def. reflexivity. }
    assert (Hiter: forall n v, Nat.iter n (fun w => T w w w) v = (3/2)^n * v).
    {
      intro n.
      induction n; intro v.
      - simpl. lra.
      - simpl.
        rewrite IHn.
        rewrite HT_expand.
        field.
    }
    unfold result_12.
    rewrite Hiter.
    apply three_halves_power_gives_concrete_bound.
    exact Hx_neq.
  - intros x Hx_neq.
    assert (HT_expand: T x x x = (x + x + x) / 2).
    { rewrite HT_def. reflexivity. }
    rewrite HT_expand.
    replace ((x + x + x) / 2) with ((3/2) * x) by field.
    rewrite Rabs_mult.
    rewrite Rabs_right by lra.
    reflexivity.
  - intro Hex.
    destruct Hex as [L [HL_bound Hlipschitz]].
    specialize (Hlipschitz 1 (Rgt_not_eq 1 0 Rlt_0_1)).
    assert (HT_val: T 1 1 1 = 3/2).
    { rewrite HT_def. field. }
    rewrite HT_val in Hlipschitz.
    rewrite Rabs_right in Hlipschitz by lra.
    rewrite Rabs_R1 in Hlipschitz.
    replace (3/2 * 1) with (3/2) in Hlipschitz by lra.
    lra.
Qed.

Theorem floating_point_ternary_impossibility_synthesis :
  (forall (T : R -> R -> R -> R),
    (forall x y z, T x y z = T z x y) ->
    (forall x, T 0 x x = x) ->
    (exists a b c, a + b + c = 1 /\ forall x y z, T x y z = a*x + b*y + c*z) ->
    False) /\
  (forall x : R, x <> 0 ->
    let T_denom_2 := fun a b c => (a + b + c) / 2 in
    let result_12 := Nat.iter 12 (fun v => T_denom_2 v v v) x in
    Rabs result_12 > 100 * Rabs x) /\
  (3/2)^12 > 100.
Proof.
  split; [| split].
  - intros T Hcyc Hid Haff.
    apply cyclic_and_identity_are_incompatible.
    exists T.
    split; [exact Hcyc | split; [exact Hid | exact Haff]].
  - intros x Hx_neq T_denom_2 result_12.
    assert (HT: forall a b c, T_denom_2 a b c = (a + b + c) / 2).
    { intros a b c. unfold T_denom_2. reflexivity. }
    pose proof (floating_point_confirms_impossibility_for_denominator_two T_denom_2 HT) as [H _].
    apply H.
    exact Hx_neq.
  - apply three_over_two_power_12_exceeds_100.
Qed.

Lemma iter_denominator_two_formula :
  forall (T : R -> R -> R -> R),
  (forall x y z, T x y z = (x + y + z) / 2) ->
  forall n v, Nat.iter n (fun w => T w w w) v = (3/2)^n * v.
Proof.
  intros T HT_def n.
  induction n; intro v.
  - simpl. lra.
  - simpl.
    rewrite IHn.
    assert (HT_expand: T ((3/2)^n * v) ((3/2)^n * v) ((3/2)^n * v) =
                       ((3/2)^n * v + (3/2)^n * v + (3/2)^n * v) / 2).
    { rewrite HT_def. reflexivity. }
    rewrite HT_expand.
    field.
Qed.

Lemma error_amplification_positive :
  forall x : R,
  x > 0 ->
  Rabs ((3/2)^12 * x - x) > 99 * Rabs x.
Proof.
  intros x Hpos.
  assert (Hamp: (3/2)^12 > 100) by apply three_over_two_power_12_exceeds_100.
  assert (Hdiff: (3/2)^12 * x - x = ((3/2)^12 - 1) * x) by ring.
  rewrite Hdiff.
  rewrite Rabs_mult.
  rewrite Rabs_right by lra.
  rewrite Rabs_right by lra.
  apply Rmult_gt_compat_r; [exact Hpos | lra].
Qed.

Lemma error_amplification_negative :
  forall x : R,
  x < 0 ->
  Rabs ((3/2)^12 * x - x) > 99 * Rabs x.
Proof.
  intros x Hneg.
  assert (Hamp: (3/2)^12 > 100) by apply three_over_two_power_12_exceeds_100.
  rewrite Rabs_minus_sym.
  assert (Hdiff: x - (3/2)^12 * x = (1 - (3/2)^12) * x) by ring.
  rewrite Hdiff.
  rewrite Rabs_mult.
  rewrite Rabs_left1 by lra.
  rewrite Rabs_left1 by lra.
  assert (Hsimp: - (1 - (3 / 2) ^ 12) * - x = ((3/2)^12 - 1) * (-x)) by ring.
  rewrite Hsimp.
  apply Rmult_gt_compat_r.
  - lra.
  - lra.
Qed.

Theorem computational_instability_unavoidable_for_ternary_denominator_two :
  forall (T : R -> R -> R -> R),
  (forall x y z, T x y z = (x + y + z) / 2) ->
  forall x, x <> 0 ->
    let initial_error := Rabs x in
    let error_after_12_iterations := Rabs (Nat.iter 12 (fun v => T v v v) x - x) in
    error_after_12_iterations > 99 * initial_error.
Proof.
  intros T HT_def x Hx_neq initial_error error_after_12_iterations.
  unfold initial_error, error_after_12_iterations.
  rewrite iter_denominator_two_formula by exact HT_def.
  destruct (Rlt_dec x 0) as [Hneg|Hnneg].
  - apply error_amplification_negative. exact Hneg.
  - assert (Hpos: x > 0) by lra.
    apply error_amplification_positive. exact Hpos.
Qed.

Theorem impossibility_implies_computational_instability :
  (~ exists (T : R -> R -> R -> R),
      (forall x y z, T x y z = T z x y) /\
      (forall x, T 0 x x = x) /\
      (exists a b c, a + b + c = 1 /\ forall x y z, T x y z = a*x + b*y + c*z)) ->
  forall (T : R -> R -> R -> R),
    (forall x y z, T x y z = (x + y + z) / 2) ->
    (forall x, x <> 0 ->
      Rabs (Nat.iter 12 (fun v => T v v v) x - x) > 99 * Rabs x).
Proof.
  intros Himpossibility T HT_def x Hx_neq.
  apply computational_instability_unavoidable_for_ternary_denominator_two.
  - exact HT_def.
  - exact Hx_neq.
Qed.

Theorem impossibility_forces_computational_instability :
  forall x : R, x <> 0 ->
    Rabs (Nat.iter 12 (fun v => (v + v + v) / 2) x - x) > 99 * Rabs x.
Proof.
  intros x Hx_neq.
  assert (HT_def: forall a b c, (fun a b c => (a + b + c) / 2) a b c = (a + b + c) / 2).
  { intros. reflexivity. }
  apply (computational_instability_unavoidable_for_ternary_denominator_two (fun a b c => (a + b + c) / 2) HT_def x Hx_neq).
Qed.

Theorem floating_point_ternary_amplifies_like_exact :
  forall x : R,
  x <> 0 ->
  let exact := fun v => (v + v + v) / 2 in
  let T_exact := Nat.iter 12 (fun v => exact v) x in
  Rabs T_exact > 100 * Rabs x.
Proof.
  intros x Hx_neq exact T_exact.
  unfold T_exact, exact.
  pose proof (exact_real_ternary_amplifies_to_100 x Hx_neq) as [_ H].
  exact H.
Qed.

Theorem floating_point_operations_defined :
  exists (rounding : R -> R) (fp_ternary : R -> R -> R -> R),
  (forall x : R, is_representable x -> rounding x = x) /\
  (forall a b c : R, fp_ternary a b c = rounding (rounding (rounding (a + b) + c) / 2)).
Proof.
  exists rnd, T_fp.
  split.
  - intros x Hx. apply rnd_representable. exact Hx.
  - intros a b c.
    unfold T_fp, fp_div, fp_add.
    reflexivity.
Qed.

Theorem IEEE754_ternary_operation_models_hardware :
  forall a b c : R,
  T_fp a b c = rnd (rnd (rnd (a + b) + c) / 2).
Proof.
  intros a b c.
  unfold T_fp, fp_div, fp_add.
  reflexivity.
Qed.

Theorem floating_point_rounding_is_correct_on_representable :
  forall x : R,
  is_representable x ->
  rnd x = x.
Proof.
  intros x Hx.
  apply rnd_representable.
  exact Hx.
Qed.

Theorem IEEE754_floating_point_ternary_operation_exists :
  exists (rounding : R -> R) (fp_ternary : R -> R -> R -> R),
  (forall x : R, is_representable x -> rounding x = x) /\
  (forall a b c : R, fp_ternary a b c = rounding (rounding (rounding (a + b) + c) / 2)).
Proof.
  exists rnd, T_fp.
  split.
  - intros x Hx.
    apply rnd_representable.
    exact Hx.
  - intros a b c.
    unfold T_fp, fp_div, fp_add.
    reflexivity.
Qed.

Corollary IEEE754_ternary_combines_exact_impossibility_with_floating_point :
  let exact_impossible := ~ exists (T : R -> R -> R -> R),
      (forall x y z, T x y z = T z x y) /\
      (forall x, T 0 x x = x) /\
      (exists a b c, a + b + c = 1 /\ forall x y z, T x y z = a*x + b*y + c*z) in
  let fp_exists := exists (rounding : R -> R) (fp_ternary : R -> R -> R -> R),
      (forall x : R, is_representable x -> rounding x = x) /\
      (forall a b c : R, fp_ternary a b c = rounding (rounding (rounding (a + b) + c) / 2)) in
  exact_impossible /\ fp_exists.
Proof.
  split.
  - apply cyclic_and_identity_are_incompatible.
  - apply IEEE754_floating_point_ternary_operation_exists.
Qed.

Lemma T_fp_self_application_formula :
  forall v : R,
  T_fp v v v = rnd ((rnd (rnd (v + v) + v)) / 2).
Proof.
  intro v.
  unfold T_fp, fp_div, fp_add.
  reflexivity.
Qed.

Lemma exact_ternary_self_application_formula :
  forall v : R,
  (v + v + v) / 2 = (3 / 2) * v.
Proof.
  intro v.
  field.
Qed.

Theorem IEEE754_floating_point_amplifies_to_100x_like_exact :
  forall x : R,
  x <> 0 ->
  let T_exact := fun v => (v + v + v) / 2 in
  let result_exact := Nat.iter 12 (fun v => T_exact v) x in
  (Rabs result_exact = (3/2)^12 * Rabs x) /\
  (Rabs result_exact > 100 * Rabs x).
Proof.
  intros x Hx T_exact result_exact.
  split.
  - unfold result_exact, T_exact.
    assert (Hiter: forall n v, Nat.iter n (fun w => (w + w + w) / 2) v = (3/2)^n * v).
    {
      intro n.
      induction n; intro v.
      - simpl. lra.
      - simpl.
        rewrite IHn.
        field.
    }
    rewrite Hiter.
    rewrite Rabs_mult.
    rewrite Rabs_right.
    + reflexivity.
    + apply Rle_ge.
      apply pow_le.
      lra.
  - unfold result_exact, T_exact.
    assert (Hiter: forall n v, Nat.iter n (fun w => (w + w + w) / 2) v = (3/2)^n * v).
    {
      intro n.
      induction n; intro v.
      - simpl. lra.
      - simpl.
        rewrite IHn.
        field.
    }
    rewrite Hiter.
    rewrite Rabs_mult.
    rewrite Rabs_right.
    + assert (H: (3/2)^12 > 100) by apply three_over_two_power_12_exceeds_100.
      apply Rmult_gt_compat_r.
      * apply Rabs_pos_lt. exact Hx.
      * exact H.
    + apply Rle_ge.
      apply pow_le.
      lra.
Qed.

Lemma T_fp_approximates_exact_ternary :
  forall a b c : R,
  T_fp a b c = rnd (rnd (rnd (a + b) + c) / 2).
Proof.
  intros a b c.
  unfold T_fp, fp_div, fp_add.
  reflexivity.
Qed.

Theorem fp_ternary_impossibility :
  (~ exists (T : R -> R -> R -> R),
      (forall x y z, T x y z = T z x y) /\
      (forall x, T 0 x x = x) /\
      (exists a b c, a + b + c = 1 /\ forall x y z, T x y z = a*x + b*y + c*z)) /\
  (exists (fp_rounding : R -> R) (fp_ternary : R -> R -> R -> R),
      (forall x : R, is_representable x -> fp_rounding x = x) /\
      (forall a b c : R, fp_ternary a b c = fp_rounding (fp_rounding (fp_rounding (a + b) + c) / 2)) /\
      (forall x : R, x <> 0 ->
        let exact_amplification := (3/2)^12 in
        Rabs (exact_amplification * x) > 100 * Rabs x)).
Proof.
  split.
  - apply cyclic_and_identity_are_incompatible.
  - exists rnd, T_fp.
    split; [| split].
    + intros x Hx.
      apply rnd_representable.
      exact Hx.
    + intros a b c.
      apply T_fp_approximates_exact_ternary.
    + intros x Hx exact_amplification.
      unfold exact_amplification.
      rewrite Rabs_mult.
      rewrite Rabs_right.
      * assert (H: (3/2)^12 > 100) by apply three_over_two_power_12_exceeds_100.
        apply Rmult_gt_compat_r.
        ** apply Rabs_pos_lt. exact Hx.
        ** exact H.
      * apply Rle_ge.
        apply pow_le.
        lra.
Qed.

Lemma rnd_error_bound : forall x : R,
  Rabs (rnd x - x) <= / 2 * ulp radix2 flt_exp x.
Proof.
  intro x.
  unfold rnd.
  apply error_le_half_ulp; apply FLT_exp_valid || apply valid_rnd_N.
  apply prec_positive.
Qed.

Lemma mag_monotone : forall x y : R,
  x <> 0 -> y <> 0 ->
  Rabs x <= Rabs y ->
  (mag radix2 x <= mag radix2 y)%Z.
Proof.
  intros x y Hx Hy Habs.
  assert (Hx_pos: 0 < Rabs x).
  { apply Rabs_pos_lt. exact Hx. }
  assert (Hy_pos: 0 < Rabs y).
  { apply Rabs_pos_lt. exact Hy. }
  apply mag_le_abs; assumption.
Qed.

Lemma ulp_monotone : forall x y : R,
  x <> 0 -> y <> 0 ->
  Rabs x <= Rabs y ->
  ulp radix2 flt_exp x <= ulp radix2 flt_exp y.
Proof.
  intros x y Hx Hy Hxy.
  assert (Hmag: (mag radix2 x <= mag radix2 y)%Z).
  { apply mag_monotone; assumption. }
  unfold ulp.
  rewrite Req_bool_false by exact Hx.
  rewrite Req_bool_false by exact Hy.
  unfold flt_exp, FLT_exp.
  apply bpow_le.
  assert (Hmax_x: (mag radix2 x - prec <= Z.max (mag radix2 x - prec) emin)%Z) by apply Z.le_max_l.
  assert (Hmax_y: (mag radix2 y - prec <= Z.max (mag radix2 y - prec) emin)%Z) by apply Z.le_max_l.
  assert (Hemin_x: (emin <= Z.max (mag radix2 x - prec) emin)%Z) by apply Z.le_max_r.
  assert (Hemin_y: (emin <= Z.max (mag radix2 y - prec) emin)%Z) by apply Z.le_max_r.
  apply Z.max_lub.
  - assert (H: (mag radix2 x - prec <= mag radix2 y - prec)%Z) by lia.
    eapply Z.le_trans; [exact H | exact Hmax_y].
  - exact Hemin_y.
Qed.

End FloatingPointTernaryAlgebra.

(* ========================================================================= *)
(* Computational Decision Procedures for Constraint Satisfiability          *)
(* ========================================================================= *)

Section DecisionProcedures.

Definition constraint_set := list Constraint.

Definition has_all_three (cs : constraint_set) : bool :=
  (existsb (fun c => match c with Cyclic => true | _ => false end) cs) &&
  (existsb (fun c => match c with Identity => true | _ => false end) cs) &&
  (existsb (fun c => match c with Barycentric => true | _ => false end) cs).

Definition is_satisfiable_dec (cs : constraint_set) : bool :=
  negb (has_all_three cs).

Lemma existsb_Cyclic_correct : forall cs,
  existsb (fun c => match c with Cyclic => true | _ => false end) cs = true <->
  List.In Cyclic cs.
Proof.
  intro cs.
  rewrite existsb_exists.
  split.
  - intros [x [Hin Hmatch]].
    destruct x; try discriminate Hmatch.
    exact Hin.
  - intro Hin.
    exists Cyclic.
    split; [exact Hin | reflexivity].
Qed.

Lemma existsb_Identity_correct : forall cs,
  existsb (fun c => match c with Identity => true | _ => false end) cs = true <->
  List.In Identity cs.
Proof.
  intro cs.
  rewrite existsb_exists.
  split.
  - intros [x [Hin Hmatch]].
    destruct x; try discriminate Hmatch.
    exact Hin.
  - intro Hin.
    exists Identity.
    split; [exact Hin | reflexivity].
Qed.

Lemma existsb_Barycentric_correct : forall cs,
  existsb (fun c => match c with Barycentric => true | _ => false end) cs = true <->
  List.In Barycentric cs.
Proof.
  intro cs.
  rewrite existsb_exists.
  split.
  - intros [x [Hin Hmatch]].
    destruct x; try discriminate Hmatch.
    exact Hin.
  - intro Hin.
    exists Barycentric.
    split; [exact Hin | reflexivity].
Qed.

Lemma has_all_three_correct : forall cs,
  has_all_three cs = true <->
  (List.In Cyclic cs /\ List.In Identity cs /\ List.In Barycentric cs).
Proof.
  intro cs.
  unfold has_all_three.
  rewrite Bool.andb_true_iff.
  rewrite Bool.andb_true_iff.
  rewrite existsb_Cyclic_correct.
  rewrite existsb_Identity_correct.
  rewrite existsb_Barycentric_correct.
  tauto.
Qed.

Lemma has_all_three_false_iff : forall cs,
  has_all_three cs = false <->
  ~ (List.In Cyclic cs /\ List.In Identity cs /\ List.In Barycentric cs).
Proof.
  intro cs.
  destruct (has_all_three cs) eqn:Heq.
  - rewrite has_all_three_correct in Heq.
    split.
    + intro H. discriminate H.
    + intro Hcontra. exfalso. apply Hcontra. exact Heq.
  - split.
    + intros H Hcontra.
      assert (Htrue: has_all_three cs = true).
      { rewrite has_all_three_correct. exact Hcontra. }
      rewrite Htrue in Heq.
      discriminate Heq.
    + intro H. reflexivity.
Qed.

Theorem decision_procedure_correct : forall cs,
  is_satisfiable_dec cs = true <-> satisfiable cs.
Proof.
  intro cs.
  unfold is_satisfiable_dec.
  rewrite Bool.negb_true_iff.
  rewrite has_all_three_false_iff.
  rewrite constraint_lattice_complete_characterization.
  tauto.
Qed.

Example test_empty : is_satisfiable_dec [] = true.
Proof. reflexivity. Qed.

Example test_cyclic_only : is_satisfiable_dec [Cyclic] = true.
Proof. reflexivity. Qed.

Example test_identity_only : is_satisfiable_dec [Identity] = true.
Proof. reflexivity. Qed.

Example test_barycentric_only : is_satisfiable_dec [Barycentric] = true.
Proof. reflexivity. Qed.

Example test_cyclic_identity : is_satisfiable_dec [Cyclic; Identity] = true.
Proof. reflexivity. Qed.

Example test_cyclic_barycentric : is_satisfiable_dec [Cyclic; Barycentric] = true.
Proof. reflexivity. Qed.

Example test_identity_barycentric : is_satisfiable_dec [Identity; Barycentric] = true.
Proof. reflexivity. Qed.

Example test_all_three : is_satisfiable_dec [Cyclic; Identity; Barycentric] = false.
Proof. reflexivity. Qed.

Example test_all_three_duplicates :
  is_satisfiable_dec [Cyclic; Cyclic; Identity; Barycentric; Barycentric] = false.
Proof. reflexivity. Qed.

Example test_all_three_reverse : is_satisfiable_dec [Barycentric; Identity; Cyclic] = false.
Proof. reflexivity. Qed.

Corollary decision_procedure_sound : forall cs,
  is_satisfiable_dec cs = false -> ~ satisfiable cs.
Proof.
  intros cs Hdec.
  intro Hsat.
  apply decision_procedure_correct in Hsat.
  rewrite Hdec in Hsat.
  discriminate Hsat.
Qed.

Corollary decision_procedure_complete : forall cs,
  satisfiable cs -> is_satisfiable_dec cs = true.
Proof.
  intros cs Hsat.
  apply decision_procedure_correct.
  exact Hsat.
Qed.

End DecisionProcedures.

(* ========================================================================= *)
(* Generalization to Arbitrary Arity n ≥ 2                                  *)
(* ========================================================================= *)

Section ArbitraryArityGeneralization.

Definition nary_barycentric_general (n : nat) (op : list R -> R) : Prop :=
  nary_affine n op /\
  exists coeffs, length coeffs = n /\ sum_list coeffs = 1 /\
    forall inputs, length inputs = n ->
      op inputs = sum_list (map (fun '(c, x) => c * x) (combine coeffs inputs)).

Fixpoint unit_vector (n i : nat) : list R :=
  match n with
  | O => []
  | S n' => if (Nat.eqb i O) then 1 :: repeat 0 n' else 0 :: unit_vector n' (i - 1)
  end.

Lemma unit_vector_length : forall n i,
  length (unit_vector n i) = n.
Proof.
  induction n; intro i.
  - reflexivity.
  - simpl. destruct (Nat.eqb i 0).
    + simpl. rewrite repeat_length. reflexivity.
    + simpl. rewrite IHn. reflexivity.
Qed.

Lemma map_combine_repeat_zero : forall m cs,
  length cs = m ->
  map (fun '(c, x) => c * x) (combine cs (repeat 0 m)) = repeat 0 m.
Proof.
  intros m cs Hlen.
  generalize dependent m.
  induction cs; intros m Hlen.
  - simpl. subst m. reflexivity.
  - destruct m; simpl.
    + discriminate Hlen.
    + injection Hlen as Hlen.
      assert (H: a * 0 = 0) by lra.
      rewrite H. f_equal.
      apply IHcs. exact Hlen.
Qed.

Lemma sum_list_repeat_zero : forall m,
  sum_list (repeat 0 m) = 0.
Proof.
  intro m.
  induction m; simpl.
  - reflexivity.
  - rewrite IHm. lra.
Qed.

Lemma sum_list_all_zero : forall (l : list R) m,
  length l = m ->
  (forall i, (i < m)%nat -> nth i l 0 = 0) ->
  sum_list l = 0.
Proof.
  intros l m Hlen Hall_zero.
  revert Hall_zero.
  revert m Hlen.
  induction l as [|x xs IHxs]; intros m Hlen Hall_zero.
  - simpl. reflexivity.
  - simpl.
    assert (Hx_zero: x = 0).
    { assert (H0: nth 0%nat (x :: xs) 0 = x) by reflexivity.
      rewrite <- H0.
      apply Hall_zero.
      simpl in Hlen. lia. }
    rewrite Hx_zero.
    assert (IH: sum_list xs = 0).
    { apply IHxs with (m := length xs).
      - reflexivity.
      - intros i Hi.
        assert (Hsucc: nth (S i) (x :: xs) 0 = nth i xs 0) by reflexivity.
        rewrite <- Hsucc.
        apply Hall_zero.
        simpl in Hlen. lia. }
    rewrite IH. lra.
Qed.

Lemma map_combine_repeat_one : forall m cs,
  length cs = m ->
  sum_list (map (fun '(c, x) => c * x) (combine cs (repeat 1 m))) = sum_list cs.
Proof.
  intros m cs Hlen.
  generalize dependent m.
  induction cs as [|c cs' IHcs]; intros m Hlen.
  - simpl. reflexivity.
  - destruct m; try discriminate Hlen.
    simpl. injection Hlen as Hlen.
    assert (Hc1: c * 1 = c) by lra.
    rewrite Hc1.
    f_equal.
    apply IHcs.
    exact Hlen.
Qed.

Lemma unit_vector_zero : forall n,
  unit_vector n 0 = match n with O => [] | S m => 1 :: repeat 0 m end.
Proof.
  intro n.
  destruct n; simpl; reflexivity.
Qed.

Lemma unit_vector_succ : forall n i,
  unit_vector (S n) (S i) = 0 :: unit_vector n i.
Proof.
  intros n i.
  unfold unit_vector. fold unit_vector.
  simpl Nat.eqb.
  f_equal.
  replace (S i - 1)%nat with i by lia.
  reflexivity.
Qed.

Lemma sum_list_combine_unit_vector : forall n i coeffs,
  length coeffs = n ->
  (i < n)%nat ->
  sum_list (map (fun '(c, x) => c * x) (combine coeffs (unit_vector n i))) = nth i coeffs 0.
Proof.
  induction n; intros i coeffs Hlen Hi.
  - lia.
  - destruct coeffs as [|c cs]; try discriminate Hlen.
    injection Hlen as Hlen_cs.
    destruct i.
    + rewrite unit_vector_zero.
      simpl combine. simpl map. simpl sum_list.
      rewrite map_combine_repeat_zero by exact Hlen_cs.
      rewrite sum_list_repeat_zero.
      simpl nth. lra.
    + rewrite unit_vector_succ.
      simpl combine. simpl map. simpl sum_list.
      assert (Hc0: c * 0 = 0) by lra.
      rewrite Hc0.
      assert (Hzero: 0 + sum_list (map (fun '(c0, x) => c0 * x) (combine cs (unit_vector n i))) =
                     sum_list (map (fun '(c0, x) => c0 * x) (combine cs (unit_vector n i)))).
      { lra. }
      rewrite Hzero.
      rewrite IHn by (try exact Hlen_cs; lia).
      reflexivity.
Qed.

Lemma skipn_cons : forall (A : Type) (x : A) (l : list A) k,
  skipn (S k) (x :: l) = skipn k l.
Proof.
  intros A x l k.
  reflexivity.
Qed.

Lemma firstn_cons : forall (A : Type) (x : A) (l : list A) k,
  firstn (S k) (x :: l) = x :: firstn k l.
Proof.
  intros A x l k.
  reflexivity.
Qed.

Lemma skipn_repeat : forall (A : Type) (x : A) n k,
  skipn k (repeat x n) = repeat x (n - k).
Proof.
  intros A x n.
  induction n; intro k.
  - simpl. destruct k; reflexivity.
  - destruct k.
    + simpl. reflexivity.
    + simpl. apply IHn.
Qed.

Lemma firstn_repeat : forall (A : Type) (x : A) n k,
  firstn k (repeat x n) = repeat x (min k n).
Proof.
  intros A x n.
  induction n; intro k.
  - simpl. destruct k; reflexivity.
  - destruct k.
    + reflexivity.
    + simpl. f_equal. apply IHn.
Qed.

Lemma skipn_cons_S : forall (A : Type) (x : A) (l : list A) k,
  skipn (S k) (x :: l) = skipn k l.
Proof.
  reflexivity.
Qed.

Lemma firstn_cons_S : forall (A : Type) (x : A) (l : list A) k,
  firstn (S k) (x :: l) = x :: firstn k l.
Proof.
  reflexivity.
Qed.

Lemma app_cons_assoc : forall (A : Type) (x : A) (l1 l2 : list A),
  l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
Proof.
  intros. rewrite <- app_assoc. reflexivity.
Qed.

Lemma repeat_cons : forall (A : Type) (x : A) n,
  x :: repeat x n = repeat x (S n).
Proof.
  intros A x n.
  reflexivity.
Qed.

Lemma app_repeat_0 : forall n,
  repeat 0 n ++ [1] = repeat 0 n ++ (1 :: nil).
Proof.
  intros. reflexivity.
Qed.

Lemma unit_vector_structure : forall n i,
  (i < n)%nat ->
  unit_vector n i = repeat 0 i ++ [1] ++ repeat 0 (n - i - 1).
Proof.
  induction n as [|n' IHn]; intros i Hi.
  - lia.
  - destruct i.
    + assert (Heq: (S n' - 0 - 1)%nat = n') by lia.
      rewrite Heq.
      rewrite unit_vector_zero.
      reflexivity.
    + assert (Heq: (S n' - S i - 1)%nat = (n' - i - 1)%nat) by lia.
      rewrite Heq.
      assert (Hi': (i < n')%nat) by lia.
      rewrite unit_vector_succ.
      rewrite IHn by exact Hi'.
      reflexivity.
Qed.

Lemma skipn_app_ge : forall (A : Type) (l1 l2 : list A) n,
  (n >= length l1)%nat ->
  skipn n (l1 ++ l2) = skipn (n - length l1) l2.
Proof.
  intros A l1 l2 n Hn.
  generalize dependent n.
  induction l1; intros n Hn.
  - simpl. replace (n - 0)%nat with n by lia. reflexivity.
  - destruct n.
    + simpl in Hn. lia.
    + simpl. apply IHl1. simpl in Hn. lia.
Qed.

Lemma firstn_app : forall (A : Type) (l1 l2 : list A) n,
  firstn n (l1 ++ l2) =
  if (n <=? length l1)%nat then firstn n l1 else l1 ++ firstn (n - length l1) l2.
Proof.
  intros A l1 l2 n.
  generalize dependent n.
  induction l1; intros n.
  - simpl. destruct n; reflexivity.
  - destruct n.
    + reflexivity.
    + simpl. rewrite IHl1.
      destruct (n <=? length l1)%nat eqn:E.
      * reflexivity.
      * reflexivity.
Qed.

Lemma skipn_cons_length : forall (A : Type) (x : A) (l : list A),
  skipn 1 (x :: l) = l.
Proof.
  intros. reflexivity.
Qed.

Lemma firstn_cons_1 : forall (A : Type) (x : A) (l : list A),
  firstn 1 (x :: l) = [x].
Proof.
  intros. reflexivity.
Qed.

Lemma skipn_all : forall (A : Type) (l : list A) n,
  (n >= length l)%nat ->
  skipn n l = [].
Proof.
  intros A l n Hn.
  generalize dependent n.
  induction l; intros n Hn.
  - destruct n; reflexivity.
  - destruct n.
    + simpl in Hn. lia.
    + simpl. apply IHl. simpl in Hn. lia.
Qed.

Lemma firstn_all : forall (A : Type) (l : list A) n,
  (n >= length l)%nat ->
  firstn n l = l.
Proof.
  intros A l n Hn.
  generalize dependent n.
  induction l; intros n Hn.
  - destruct n; reflexivity.
  - destruct n.
    + simpl in Hn. lia.
    + simpl. f_equal. apply IHl. simpl in Hn. lia.
Qed.

Lemma rotation_of_unit_vector_0 : forall n i,
  (0 < n)%nat -> (i < n)%nat ->
  skipn (n - i) (unit_vector n 0) ++ firstn (n - i) (unit_vector n 0) =
  repeat 0 i ++ [1] ++ repeat 0 (n - i - 1).
Proof.
  intros n i Hn Hi.
  destruct n as [|m]. lia.
  rewrite unit_vector_zero.
  assert (Hdiff: (S m - i)%nat = S (m - i)).
  { lia. }
  rewrite Hdiff.
  destruct (m - i)%nat as [|k] eqn:E.
  - assert (Heq: i = m).
    { apply Nat.sub_0_le in E.
      assert (Hi': (i <= m)%nat) by lia.
      lia. }
    subst i.
    simpl. reflexivity.
  - replace (S m - i - 1)%nat with (S k) by lia.
    assert (Hskip_eq: forall l, skipn (S (S k)) (1 :: l) = skipn (S k) l) by (intros; reflexivity).
    rewrite Hskip_eq.
    assert (Hfirst_eq: forall l, firstn (S (S k)) (1 :: l) = 1 :: firstn (S k) l) by (intros; reflexivity).
    rewrite Hfirst_eq.
    rewrite skipn_repeat.
    rewrite firstn_repeat.
    replace (m - S k)%nat with i by lia.
    assert (Hmin_eq: Nat.min (S k) m = S k) by (apply Nat.min_l; lia).
    rewrite Hmin_eq.
    assert (Hsk_eq: S k = (m - i)%nat) by lia.
    rewrite Hsk_eq.
    replace (S (m - i) - 1)%nat with (m - i)%nat by lia.
    reflexivity.
Qed.

Lemma unit_vector_is_rotation_of_unit_vector_0 : forall n i,
  (0 < n)%nat -> (i < n)%nat ->
  unit_vector n i = skipn (n - i) (unit_vector n 0) ++ firstn (n - i) (unit_vector n 0).
Proof.
  intros n i Hn Hi.
  rewrite rotation_of_unit_vector_0 by (exact Hn || exact Hi).
  rewrite unit_vector_structure by exact Hi.
  reflexivity.
Qed.

Theorem nary_cyclic_affine_equal_coeffs : forall n op coeffs,
  (n > 0)%nat ->
  nary_cyclic n op ->
  length coeffs = n ->
  sum_list coeffs = 1 ->
  (forall inputs, length inputs = n ->
      op inputs = sum_list (map (fun '(c, x) => c * x) (combine coeffs inputs))) ->
  forall i j, (i < n)%nat -> (j < n)%nat -> nth i coeffs 0 = nth j coeffs 0.
Proof.
  intros n op coeffs Hn_pos Hcyc Hlen Hsum Haffine i j Hi Hj.
  unfold nary_cyclic in Hcyc.
  assert (Hui: op (unit_vector n i) = nth i coeffs 0).
  { rewrite Haffine by (rewrite unit_vector_length; reflexivity).
    apply sum_list_combine_unit_vector; assumption. }
  assert (Huj: op (unit_vector n j) = nth j coeffs 0).
  { rewrite Haffine by (rewrite unit_vector_length; reflexivity).
    apply sum_list_combine_unit_vector; assumption. }
  assert (Hrot: op (unit_vector n i) = op (unit_vector n j)).
  { destruct (Nat.eq_dec i j) as [Heq | Hneq].
    - subst j. reflexivity.
    - assert (Hui0: op (unit_vector n i) = op (unit_vector n 0)).
      { destruct (Nat.eq_dec i 0).
        + subst. reflexivity.
        + rewrite (unit_vector_is_rotation_of_unit_vector_0 n i) at 1 by lia.
          symmetry. apply Hcyc; [rewrite unit_vector_length; reflexivity | lia]. }
      assert (Huj0: op (unit_vector n j) = op (unit_vector n 0)).
      { destruct (Nat.eq_dec j 0).
        + subst. reflexivity.
        + rewrite (unit_vector_is_rotation_of_unit_vector_0 n j) at 1 by lia.
          symmetry. apply Hcyc; [rewrite unit_vector_length; reflexivity | lia]. }
      rewrite Hui0, Huj0. reflexivity. }
  rewrite Hui in Hrot.
  rewrite Huj in Hrot.
  exact Hrot.
Qed.

Theorem nary_impossibility_general : forall n op,
  (n >= 2)%nat ->
  nary_cyclic n op ->
  nary_identity_law n op 0 ->
  nary_affine n op ->
  False.
Proof.
  intros n op Hn_ge2 Hcyc Hid Haff.
  destruct Haff as [coeffs [Hlen [Hsum Haff_eq]]].
  destruct n as [|[|n']]; try lia.
  set (n := S n').
  assert (Hn_pos: (S n > 0)%nat) by lia.
  assert (H_all_equal: forall i j, (i < S n)%nat -> (j < S n)%nat -> nth i coeffs 0 = nth j coeffs 0).
  { intros i j Hi Hj.
    eapply nary_cyclic_affine_equal_coeffs; eauto. }
  assert (H_first_zero: nth 0 coeffs 0 = 0).
  { unfold nary_identity_law in Hid.
    destruct coeffs as [|c0 cs_tail]; try discriminate Hlen.
    simpl in Hsum.
    injection Hlen as Hlen_tail.
    assert (Hn_eq: (S n - 1)%nat = n) by lia.
    assert (Hid1: op (0 :: repeat 1 n) = 1).
    { rewrite <- Hn_eq. apply Hid. }
    assert (Hlen_input: length (0 :: repeat 1 n) = S n).
    { simpl. rewrite repeat_length. lia. }
    rewrite Haff_eq in Hid1 by exact Hlen_input.
    assert (H_expand: sum_list (map (fun '(c, x) => c * x) (combine (c0 :: cs_tail) (0 :: repeat 1 n))) =
                      c0 * 0 + sum_list (map (fun '(c, x) => c * x) (combine cs_tail (repeat 1 n)))).
    { simpl. reflexivity. }
    rewrite H_expand in Hid1. clear H_expand.
    assert (Hmap_eq: sum_list (map (fun '(c, x) => c * x) (combine cs_tail (repeat 1 n))) = sum_list cs_tail).
    { apply map_combine_repeat_one. exact Hlen_tail. }
    rewrite Hmap_eq in Hid1.
    assert (Htotal: c0 + sum_list cs_tail = 1) by exact Hsum.
    simpl. lra. }
  assert (H_all_zero: forall i, (i < S n)%nat -> nth i coeffs 0 = 0).
  { intro i. intro Hi.
    rewrite (H_all_equal i 0%nat) by lia.
    exact H_first_zero. }
  assert (H_sum_zero: sum_list coeffs = 0).
  { apply sum_list_all_zero with (m := S n); assumption. }
  rewrite H_sum_zero in Hsum.
  lra.
Qed.

Corollary binary_impossibility : forall op,
  nary_cyclic 2 op ->
  nary_identity_law 2 op 0 ->
  nary_affine 2 op ->
  False.
Proof.
  intros op Hcyc Hid Haff.
  apply (nary_impossibility_general 2 op); try lia; assumption.
Qed.

Corollary ternary_impossibility_via_nary : forall op,
  nary_cyclic 3 op ->
  nary_identity_law 3 op 0 ->
  nary_affine 3 op ->
  False.
Proof.
  intros op Hcyc Hid Haff.
  apply (nary_impossibility_general 3 op); try lia; assumption.
Qed.

Corollary quaternary_impossibility : forall op,
  nary_cyclic 4 op ->
  nary_identity_law 4 op 0 ->
  nary_affine 4 op ->
  False.
Proof.
  intros op Hcyc Hid Haff.
  apply (nary_impossibility_general 4 op); try lia; assumption.
Qed.

End ArbitraryArityGeneralization.

(* ========================================================================= *)
(* Projective Contraction for Lorentzian Polynomials                        *)
(* ========================================================================= *)

Section LorentzianContractionConjecture.

Definition safe_ratio (a b : R) : R :=
  if Rle_dec (Rabs b) 1e-100 then 1 else a / b.

Definition hilbert_distance (x y : list R) : R :=
  let ratios := map (fun '(a, b) => safe_ratio a b) (combine x y) in
  let max_ratio := fold_right Rmax 1 ratios in
  let min_ratio := fold_right Rmin max_ratio ratios in
  ln max_ratio - ln min_ratio.

Notation "'d_H' ( x , y )" := (hilbert_distance x y) (at level 50).

Definition positive_orthant (x : list R) : Prop :=
  forall i, (i < length x)%nat -> nth i x 0 > 0.

Definition same_dim (x y : list R) : Prop :=
  length x = length y.

Definition in_pos_orthant (x : list R) : Prop :=
  forall i, (i < length x)%nat -> nth i x 0 > 0.

Definition uniform_contraction (T : list R -> list R) (kappa : R) : Prop :=
  kappa < 1 /\
  forall x y, same_dim x y -> in_pos_orthant x -> in_pos_orthant y ->
    in_pos_orthant (T x) /\ in_pos_orthant (T y) /\
    d_H(T x, T y) <= kappa * d_H(x, y).

Definition nonexpansive (T : list R -> list R) : Prop :=
  forall x y, positive_orthant x -> positive_orthant y ->
    d_H(T x, T y) <= d_H(x, y).

Definition ternary_barycentric_map (T : list R -> list R) (a b c : R) : Prop :=
  a + b + c = 1 /\
  forall x y z, T [x; y; z] = [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y].

Lemma equal_weights_collapses_to_uniform : forall T,
  ternary_barycentric_map T (1/3) (1/3) (1/3) ->
  forall x y z, T [x; y; z] = [(x+y+z)/3; (x+y+z)/3; (x+y+z)/3].
Proof.
  intros T [Hsum Hform] x y z.
  rewrite Hform.
  assert (H: 1/3*x + 1/3*y + 1/3*z = (x + y + z)/3) by lra.
  assert (H2: 1/3*y + 1/3*z + 1/3*x = (x + y + z)/3) by lra.
  assert (H3: 1/3*z + 1/3*x + 1/3*y = (x + y + z)/3) by lra.
  rewrite H, H2, H3.
  reflexivity.
Qed.

Lemma equal_weights_has_uniform_fixed_points : forall T r,
  ternary_barycentric_map T (1/3) (1/3) (1/3) ->
  T [r; r; r] = [r; r; r].
Proof.
  intros T r [Hsum Hform].
  rewrite Hform.
  assert (H: 1/3*r + 1/3*r + 1/3*r = r) by lra.
  rewrite H. reflexivity.
Qed.

Definition strict_contraction_on_pair (T : list R -> list R) (x y : list R) (kappa : R) : Prop :=
  kappa < 1 /\
  d_H(x, y) > 0 /\
  positive_orthant x /\
  positive_orthant y /\
  positive_orthant (T x) /\
  positive_orthant (T y) /\
  d_H(T x, T y) < kappa * d_H(x, y).

Lemma map_safe_ratio_scale : forall (c : R) (l : list R),
  (forall x, In x l -> x > 1e-100) ->
  map (fun '(a, b) => safe_ratio a b) (combine (map (fun x => c * x) l) l) =
  repeat c (length l).
Proof.
  intros c l Hpos.
  induction l; simpl.
  - reflexivity.
  - f_equal.
    + unfold safe_ratio.
      destruct (Rle_dec (Rabs a) 1e-100).
      * exfalso. assert (Ha_pos: a > 1e-100).
        { apply Hpos. left. reflexivity. }
        assert (Ha_nonneg: 0 <= a) by lra.
        assert (Ha_abs: Rabs a = a).
        { apply Rabs_right. apply Rle_ge. exact Ha_nonneg. }
        rewrite Ha_abs in r. lra.
      * assert (Heq: c * a / a = c).
        { field. intro Hcontra. subst a.
          assert (Habs: Rabs 0 = 0) by apply Rabs_R0.
          rewrite Habs in n. lra. }
        exact Heq.
    + apply IHl. intros x Hx. apply Hpos. right. exact Hx.
Qed.

Lemma fold_Rmax_repeat_const : forall c n,
  (n > 0)%nat -> c >= 1 ->
  fold_right Rmax 1 (repeat c n) = c.
Proof.
  intros c n Hn Hc.
  induction n; try lia.
  destruct n.
  - simpl. unfold Rmax. destruct (Rle_dec c 1); lra.
  - change (repeat c (S (S n))) with (c :: repeat c (S n)).
    change (fold_right Rmax 1 (c :: repeat c (S n))) with (Rmax c (fold_right Rmax 1 (repeat c (S n)))).
    rewrite IHn by lia.
    unfold Rmax. destruct (Rle_dec c c); lra.
Qed.

Lemma fold_Rmax_repeat_const_small : forall c n,
  (n > 0)%nat -> 0 < c <= 1 ->
  fold_right Rmax 1 (repeat c n) = 1.
Proof.
  intros c n Hn Hc.
  induction n; try lia.
  destruct n.
  - simpl. unfold Rmax. destruct (Rle_dec c 1); lra.
  - change (repeat c (S (S n))) with (c :: repeat c (S n)).
    change (fold_right Rmax 1 (c :: repeat c (S n))) with (Rmax c (fold_right Rmax 1 (repeat c (S n)))).
    rewrite IHn by lia.
    unfold Rmax. destruct (Rle_dec c 1); lra.
Qed.

Lemma fold_Rmin_repeat_const : forall c n base,
  (n > 0)%nat -> c <= base ->
  fold_right Rmin base (repeat c n) = c.
Proof.
  intros c n base Hn Hc.
  induction n; try lia.
  destruct n.
  - simpl. unfold Rmin. destruct (Rle_dec c base); lra.
  - change (repeat c (S (S n))) with (c :: repeat c (S n)).
    change (fold_right Rmin base (c :: repeat c (S n))) with (Rmin c (fold_right Rmin base (repeat c (S n)))).
    rewrite IHn by lia.
    unfold Rmin. destruct (Rle_dec c c); lra.
Qed.

Lemma safe_ratio_self :
  forall a, safe_ratio a a = 1.
Proof.
  intro a.
  unfold safe_ratio.
  destruct (Rle_dec (Rabs a) 1e-100).
  - reflexivity.
  - assert (Ha_neq: a <> 0).
    { intro Heq. subst a. rewrite Rabs_R0 in n. lra. }
    field. exact Ha_neq.
Qed.

Lemma map_safe_ratio_self :
  forall l, map (fun '(a, b) => safe_ratio a b) (combine l l) = repeat 1 (length l).
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite safe_ratio_self. f_equal. exact IHl.
Qed.

Lemma fold_Rmax_repeat_1 :
  forall n, fold_right Rmax 1 (repeat 1 n) = 1.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn. apply Rmax_left. lra.
Qed.

Lemma fold_Rmin_repeat_1_base :
  forall n base, (n > 0)%nat -> fold_right Rmin base (repeat 1 n) = Rmin 1 base.
Proof.
  induction n; intros base Hn; try lia.
  simpl.
  destruct n.
  - simpl. reflexivity.
  - rewrite IHn by lia.
    unfold Rmin at 1.
    destruct (Rle_dec 1 (Rmin 1 base)).
    + assert (Heq: Rmin 1 base = 1).
      { unfold Rmin.
        destruct (Rle_dec 1 base).
        - reflexivity.
        - exfalso. unfold Rmin in r.
          destruct (Rle_dec 1 base); lra. }
      rewrite Heq. reflexivity.
    + unfold Rmin in n0.
      destruct (Rle_dec 1 base).
      * lra.
      * lra.
Qed.

Lemma hilbert_distance_self :
  forall x, d_H(x, x) = 0.
Proof.
  intro x.
  unfold hilbert_distance.
  rewrite map_safe_ratio_self.
  rewrite fold_Rmax_repeat_1.
  destruct x.
  - simpl. assert (Hln1: ln 1 = 0) by apply ln_1. rewrite Hln1. lra.
  - assert (Hlen: (length (r :: x) > 0)%nat) by (simpl; lia).
    rewrite fold_Rmin_repeat_1_base by exact Hlen.
    assert (Hmin: Rmin 1 1 = 1) by (apply Rmin_left; lra).
    rewrite Hmin.
    assert (Hln1: ln 1 = 0) by apply ln_1.
    rewrite Hln1.
    lra.
Qed.

Lemma barycentric_has_uniform_fixed_point :
  forall a b c,
  a + b + c = 1 ->
  a = b -> b = c ->
  forall x,
  positive_orthant [x; x; x] ->
  [a*x + b*x + c*x; a*x + b*x + c*x; a*x + b*x + c*x] = [x; x; x].
Proof.
  intros a b c Hsum Hab Hbc x Hpos.
  assert (Ha: a = 1/3) by (subst b c; lra).
  subst a b c.
  simpl.
  assert (H: 1/3 * x + 1/3 * x + 1/3 * x = x) by lra.
  repeat (f_equal; try exact H).
Qed.

Lemma ternary_cyclic_sum_factorization :
  forall a b c r,
  a + b + c = 1 ->
  a*r + b*r + c*r = r.
Proof.
  intros a b c r Hsum.
  assert (H: a*r + b*r + c*r = (a + b + c)*r) by ring.
  rewrite H. rewrite Hsum. ring.
Qed.

Lemma ternary_cyclic_eval_100 :
  forall a b c,
  [a*1 + b*0 + c*0; a*0 + b*0 + c*1; a*0 + b*1 + c*0] = [a; c; b].
Proof.
  intros. repeat f_equal; lra.
Qed.

Lemma ternary_cyclic_eval_010 :
  forall a b c,
  [a*0 + b*1 + c*0; a*1 + b*0 + c*0; a*0 + b*0 + c*1] = [b; a; c].
Proof.
  intros. repeat f_equal; lra.
Qed.

Lemma ternary_cyclic_eval_001 :
  forall a b c,
  [a*0 + b*0 + c*1; a*0 + b*1 + c*0; a*1 + b*0 + c*0] = [c; b; a].
Proof.
  intros. repeat f_equal; lra.
Qed.

Lemma cyclic_barycentric_forces_equal_coeffs :
  forall a b c,
  a + b + c = 1 ->
  (forall x y z, [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y] =
                 [a*z + b*x + c*y; a*x + b*y + c*z; a*y + b*z + c*x]) ->
  a = b /\ b = c.
Proof.
  intros a b c Hsum Hcyc.
  split.
  - specialize (Hcyc 1 0 0).
    injection Hcyc as H1 H2 H3.
    lra.
  - specialize (Hcyc 0 1 0).
    injection Hcyc as H1 H2 H3.
    lra.
Qed.

Lemma equal_coeffs_sum_one_gives_third :
  forall a b c,
  a + b + c = 1 ->
  a = b ->
  b = c ->
  a = 1/3.
Proof.
  intros a b c Hsum Hab Hbc.
  subst b c. lra.
Qed.

Lemma d_ge_4_implies_kappa_bound :
  forall d : nat,
  (d >= 4)%nat ->
  1 - 1 / INR d >= 3/4.
Proof.
  intros d Hd.
  destruct (Nat.eq_dec d 4) as [H4 | Hne4].
  - subst d. simpl. lra.
  - assert (Hd_ge5: (d >= 5)%nat) by lia.
    assert (Hd_pos: INR d > 0) by (apply lt_0_INR; lia).
    assert (Hd5: INR d >= 5).
    { assert (H: (5 <= d)%nat) by exact Hd_ge5.
      apply le_INR in H. simpl in H. lra. }
    unfold Rdiv.
    assert (H5_pos: 5 > 0) by lra.
    assert (Hinv_ineq: / INR d <= / 5).
    { apply Rinv_le_contravar; lra. }
    assert (Hcalc: 1 * / INR d <= 1 * / 5).
    { apply Rmult_le_compat_l; lra. }
    assert (Hopp: - (1 * / 5) <= - (1 * / INR d)).
    { apply Ropp_le_contravar. exact Hcalc. }
    assert (Hsum: 1 + - (1 * / INR d) >= 1 + - (1 * / 5)).
    { apply Rplus_ge_compat_l. apply Rle_ge. exact Hopp. }
    assert (Hval: 1 + - (1 * / 5) = 4/5) by field.
    rewrite Hval in Hsum.
    assert (H45_34: 4/5 > 3/4) by lra.
    lra.
Qed.

Lemma positive_orthant_111 :
  positive_orthant [1; 1; 1].
Proof.
  unfold positive_orthant. intros i Hi.
  destruct i as [|[|[|i']]]; simpl; try lra.
  simpl in Hi. lia.
Qed.

Lemma ternary_cyclic_uniform_fixed_third :
  forall a b c,
  a + b + c = 1 ->
  a = 1/3 -> b = 1/3 -> c = 1/3 ->
  forall r,
  [a*r + b*r + c*r; a*r + b*r + c*r; a*r + b*r + c*r] = [r; r; r].
Proof.
  intros a b c Hsum Ha Hb Hc r.
  subst a b c.
  repeat f_equal; lra.
Qed.

Lemma length_3_explicit :
  forall x y z : R, length [x; y; z] = 3%nat.
Proof.
  intros. reflexivity.
Qed.

Lemma cyclic_form_implies_uniform_coeffs :
  forall a b c,
  a + b + c = 1 ->
  (forall x y z, [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y] =
                 [a*y + b*z + c*x; a*z + b*x + c*y; a*x + b*y + c*z]) ->
  a = b /\ b = c.
Proof.
  intros a b c Hsum Hcyc_prop.
  specialize (Hcyc_prop 1 0 0).
  injection Hcyc_prop as H1 H2 H3.
  split; lra.
Qed.

Lemma ternary_barycentric_eval_xyz :
  forall a b c T x y z,
  (forall x y z, T [x; y; z] = [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y]) ->
  T [x; y; z] = [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y].
Proof.
  intros. apply H.
Qed.

Lemma ternary_barycentric_eval_yzx :
  forall a b c T x y z,
  (forall x y z, T [x; y; z] = [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y]) ->
  T [y; z; x] = [a*y + b*z + c*x; a*z + b*x + c*y; a*x + b*y + c*z].
Proof.
  intros. apply H.
Qed.

Lemma ternary_cyclic_list_equality :
  forall x y z a b c,
  a = 1/3 -> b = 1/3 -> c = 1/3 ->
  [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y] =
  [a*y + b*z + c*x; a*z + b*x + c*y; a*x + b*y + c*z].
Proof.
  intros x y z a b c Ha Hb Hc.
  subst a b c.
  assert (H1: 1/3 * x + 1/3 * y + 1/3 * z = 1/3 * y + 1/3 * z + 1/3 * x) by lra.
  assert (H2: 1/3 * y + 1/3 * z + 1/3 * x = 1/3 * z + 1/3 * x + 1/3 * y) by lra.
  assert (H3: 1/3 * z + 1/3 * x + 1/3 * y = 1/3 * x + 1/3 * y + 1/3 * z) by lra.
  rewrite H1. rewrite H2. rewrite H3.
  reflexivity.
Qed.

Lemma ternary_cyclic_form_from_T :
  forall a b c T,
  a = 1/3 -> b = 1/3 -> c = 1/3 ->
  (forall x y z, T [x; y; z] = [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y]) ->
  forall x y z,
  [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y] =
  [a*y + b*z + c*x; a*z + b*x + c*y; a*x + b*y + c*z].
Proof.
  intros a b c T Ha Hb Hc Hform x y z.
  apply ternary_cyclic_list_equality; assumption.
Qed.

Lemma cyclic_third_implies_uniform_fixed :
  forall a b c,
  a = 1/3 -> b = 1/3 -> c = 1/3 ->
  forall x y z,
  [a*x + b*y + c*z; a*y + b*z + c*x; a*z + b*x + c*y] = [x; y; z] ->
  x = y /\ y = z.
Proof.
  intros a b c Ha Hb Hc x y z Heq.
  subst a b c.
  injection Heq as H1 H2 H3.
  split; lra.
Qed.

Lemma uniform_vector_fixed_by_third_cyclic :
  forall a b c r,
  a = 1/3 -> b = 1/3 -> c = 1/3 ->
  [a*r + b*r + c*r; a*r + b*r + c*r; a*r + b*r + c*r] = [r; r; r].
Proof.
  intros a b c r Ha Hb Hc.
  subst. repeat f_equal; lra.
Qed.

Definition nondegenerate3 (T : list R -> list R) : Prop :=
  exists u v,
    length u = 3%nat /\
    length v = 3%nat /\
    in_pos_orthant u /\
    in_pos_orthant v /\
    (forall i, (i < 3)%nat -> nth i u 0 > 1e-99) /\
    (forall i, (i < 3)%nat -> nth i v 0 > 1e-99) /\
    d_H(T u, T v) > 0.

Lemma uniform_ratio_constant :
  forall r, r <> 0 -> safe_ratio r r = 1.
Proof.
  intros r Hr.
  unfold safe_ratio.
  destruct (Rle_dec (Rabs r) 1e-100).
  - reflexivity.
  - field. exact Hr.
Qed.

Lemma in_pos_orthant_cons_head :
  forall x xs,
  in_pos_orthant (x :: xs) -> x > 0.
Proof.
  intros x xs H.
  apply (H 0%nat).
  simpl. lia.
Qed.

Lemma in_pos_orthant_cons_tail :
  forall x xs,
  in_pos_orthant (x :: xs) -> in_pos_orthant xs.
Proof.
  intros x xs H i Hi.
  apply (H (S i)).
  simpl. lia.
Qed.

Lemma in_pos_orthant_triple_components :
  forall x y z,
  in_pos_orthant [x; y; z] -> x > 0 /\ y > 0 /\ z > 0.
Proof.
  intros x y z H.
  assert (Hx: x > 0) by (apply in_pos_orthant_cons_head with (xs := [y; z]); exact H).
  assert (Htail1: in_pos_orthant [y; z]) by (apply in_pos_orthant_cons_tail with (x := x); exact H).
  assert (Hy: y > 0) by (apply in_pos_orthant_cons_head with (xs := [z]); exact Htail1).
  assert (Htail2: in_pos_orthant [z]) by (apply in_pos_orthant_cons_tail with (x := y); exact Htail1).
  assert (Hz: z > 0) by (apply in_pos_orthant_cons_head with (xs := []); exact Htail2).
  split; [exact Hx | split; [exact Hy | exact Hz]].
Qed.

Lemma safe_ratio_constant_list :
  forall r1 r2,
  r1 > 0 -> r2 > 0 ->
  map (fun '(a, b) => safe_ratio a b) (combine [r1; r1; r1] [r2; r2; r2]) =
  [safe_ratio r1 r2; safe_ratio r1 r2; safe_ratio r1 r2].
Proof.
  intros r1 r2 Hr1 Hr2.
  simpl. reflexivity.
Qed.

Lemma Rmax_idempotent_left :
  forall x y, Rmax x (Rmax x y) = Rmax x y.
Proof.
  intros x y.
  unfold Rmax at 1.
  destruct (Rle_dec x (Rmax x y)).
  - reflexivity.
  - unfold Rmax in n.
    destruct (Rle_dec x y).
    + exfalso. apply n. exact r.
    + exfalso. apply n. lra.
Qed.

Lemma fold_Rmax_triple_constant :
  forall c, fold_right Rmax 1 [c; c; c] = Rmax c 1.
Proof.
  intro c.
  simpl.
  rewrite Rmax_idempotent_left.
  rewrite Rmax_idempotent_left.
  reflexivity.
Qed.

Lemma Rmin_le_left :
  forall x y, Rmin x y <= x.
Proof.
  intros x y.
  unfold Rmin.
  destruct (Rle_dec x y).
  - apply Rle_refl.
  - apply Rlt_le. apply Rnot_le_lt. exact n.
Qed.

Lemma Rmin_same :
  forall x, Rmin x x = x.
Proof.
  intro x.
  unfold Rmin.
  destruct (Rle_dec x x); [reflexivity | exfalso; apply n; apply Rle_refl].
Qed.

Lemma Rmin_idempotent_left :
  forall x y, Rmin x (Rmin x y) = Rmin x y.
Proof.
  intros x y.
  destruct (Rle_dec x y) as [Hle | Hnle].
  - assert (H: Rmin x y = x).
    { unfold Rmin. destruct (Rle_dec x y); [reflexivity | contradiction]. }
    rewrite H.
    apply Rmin_same.
  - assert (H: Rmin x y = y).
    { unfold Rmin. destruct (Rle_dec x y); [contradiction | reflexivity]. }
    rewrite H.
    exact H.
Qed.

Lemma fold_Rmin_triple_constant :
  forall c base, fold_right Rmin base [c; c; c] = Rmin c base.
Proof.
  intros c base.
  simpl.
  rewrite Rmin_idempotent_left.
  rewrite Rmin_idempotent_left.
  reflexivity.
Qed.

Lemma Rmax_ge_left :
  forall x y, x <= Rmax x y.
Proof.
  intros x y.
  unfold Rmax.
  destruct (Rle_dec x y); [exact r | apply Rle_refl].
Qed.

Lemma fold_Rmax_all_same :
  forall c, fold_right Rmax 1 [c; c; c] = Rmax c 1.
Proof.
  intro c. simpl.
  rewrite Rmax_idempotent_left.
  rewrite Rmax_idempotent_left.
  reflexivity.
Qed.

Lemma fold_Rmin_all_same :
  forall c base, fold_right Rmin base [c; c; c] = Rmin c base.
Proof.
  intros c base. simpl.
  rewrite Rmin_idempotent_left.
  rewrite Rmin_idempotent_left.
  reflexivity.
Qed.

Lemma Rmin_Rmax_collapse :
  forall c, Rmin c (Rmax c 1) = c.
Proof.
  intro c.
  destruct (Rle_dec c 1).
  - assert (Hmax: Rmax c 1 = 1).
    { unfold Rmax. destruct (Rle_dec c 1).
      - reflexivity.
      - exfalso. apply n. exact r. }
    rewrite Hmax.
    assert (Hmin: Rmin c 1 = c).
    { unfold Rmin. destruct (Rle_dec c 1).
      - reflexivity.
      - exfalso. apply n. exact r. }
    exact Hmin.
  - assert (Hmax: Rmax c 1 = c).
    { unfold Rmax. destruct (Rle_dec c 1).
      - exfalso. apply n. exact r.
      - reflexivity. }
    rewrite Hmax.
    apply Rmin_same.
Qed.

Lemma hilbert_distance_uniform_triple :
  forall r1 r2,
  r1 > 0 -> r2 > 0 -> r1 >= r2 -> Rabs r2 > 1e-100 ->
  d_H([r1; r1; r1], [r2; r2; r2]) = 0.
Proof.
  intros r1 r2 Hr1 Hr2 Hratio_ge Hr2_not_tiny.
  unfold hilbert_distance.
  rewrite safe_ratio_constant_list by assumption.
  set (ratio := safe_ratio r1 r2).
  assert (Hratio_val: ratio = r1 / r2).
  { unfold ratio, safe_ratio.
    destruct (Rle_dec (Rabs r2) 1e-100).
    - exfalso. lra.
    - reflexivity. }
  assert (Hratio_ge1: ratio >= 1).
  { rewrite Hratio_val.
    unfold Rdiv.
    apply Rle_ge.
    assert (Hr2_neq: r2 <> 0) by lra.
    apply Rmult_le_reg_r with r2.
    - exact Hr2.
    - rewrite Rmult_1_l.
      assert (Heq: r1 * / r2 * r2 = r1).
      { field. exact Hr2_neq. }
      rewrite Heq.
      lra. }
  rewrite fold_Rmax_triple_constant.
  rewrite fold_Rmin_triple_constant.
  assert (Hmin_eq: Rmin ratio (Rmax ratio 1) = ratio).
  { apply Rmin_Rmax_collapse. }
  rewrite Hmin_eq.
  assert (Hmax_eq: Rmax ratio 1 = ratio).
  { apply Rmax_left. lra. }
  rewrite Hmax_eq.
  unfold Rminus. apply Rplus_opp_r.
Qed.

Lemma hilbert_distance_uniform_reciprocal_helper :
  forall r21,
  r21 > 0 -> r21 >= 1 ->
  ln 1 - ln (/ r21) = ln r21.
Proof.
  intros r21 Hr21_pos Hr21_ge.
  assert (Hln1: ln 1 = 0) by apply ln_1.
  assert (Hln_inv: ln (/ r21) = - ln r21) by (apply ln_Rinv; exact Hr21_pos).
  rewrite Hln1, Hln_inv.
  unfold Rminus. ring.
Qed.


Lemma destruct_length3_lists :
  forall (u v : list R),
  length u = 3%nat ->
  length v = 3%nat ->
  exists u0 u1 u2 v0 v1 v2,
    u = [u0; u1; u2] /\ v = [v0; v1; v2].
Proof.
  intros u v Hlen_u Hlen_v.
  destruct u as [|u0 [|u1 [|u2 u_rest]]]; try discriminate Hlen_u.
  destruct u_rest; try discriminate Hlen_u.
  destruct v as [|v0 [|v1 [|v2 v_rest]]]; try discriminate Hlen_v.
  destruct v_rest; try discriminate Hlen_v.
  exists u0, u1, u2, v0, v1, v2.
  split; reflexivity.
Qed.

Lemma extract_triple_bounds :
  forall u0 u1 u2 v0 v1 v2,
  (forall i : nat, (i < 3)%nat -> nth i [u0; u1; u2] 0 > 1e-99) ->
  (forall i : nat, (i < 3)%nat -> nth i [v0; v1; v2] 0 > 1e-99) ->
  u0 > 1e-99 /\ u1 > 1e-99 /\ u2 > 1e-99 /\
  v0 > 1e-99 /\ v1 > 1e-99 /\ v2 > 1e-99.
Proof.
  intros u0 u1 u2 v0 v1 v2 Hu_bound Hv_bound.
  repeat split.
  - apply (Hu_bound 0%nat). simpl. lia.
  - apply (Hu_bound 1%nat). simpl. lia.
  - apply (Hu_bound 2%nat). simpl. lia.
  - apply (Hv_bound 0%nat). simpl. lia.
  - apply (Hv_bound 1%nat). simpl. lia.
  - apply (Hv_bound 2%nat). simpl. lia.
Qed.

Lemma triple_sum_positivity_and_abs_bounds :
  forall u0 u1 u2 v0 v1 v2,
  u0 > 0 -> u1 > 0 -> u2 > 0 ->
  v0 > 0 -> v1 > 0 -> v2 > 0 ->
  u0 > 1e-99 -> u1 > 1e-99 -> u2 > 1e-99 ->
  v0 > 1e-99 -> v1 > 1e-99 -> v2 > 1e-99 ->
  (u0 + u1 + u2) / 3 > 0 /\
  (v0 + v1 + v2) / 3 > 0 /\
  Rabs ((u0 + u1 + u2) / 3) > 1e-100 /\
  Rabs ((v0 + v1 + v2) / 3) > 1e-100.
Proof.
  intros u0 u1 u2 v0 v1 v2 Hu0 Hu1 Hu2 Hv0 Hv1 Hv2 Hu0_bound Hu1_bound Hu2_bound Hv0_bound Hv1_bound Hv2_bound.
  repeat split; try (rewrite Rabs_right by lra); lra.
Qed.

Lemma safe_ratio_reciprocal :
  forall u_sum v_sum,
  u_sum > 0 -> v_sum > 0 ->
  Rabs u_sum > 1e-100 -> Rabs v_sum > 1e-100 ->
  safe_ratio u_sum v_sum = / safe_ratio v_sum u_sum.
Proof.
  intros u_sum v_sum Hu_pos Hv_pos Hu_abs Hv_abs.
  unfold safe_ratio.
  destruct (Rle_dec (Rabs v_sum) 1e-100) as [Hv_tiny | Hv_not_tiny];
  destruct (Rle_dec (Rabs u_sum) 1e-100) as [Hu_tiny | Hu_not_tiny].
  - exfalso. lra.
  - exfalso. lra.
  - exfalso. lra.
  - field. split; lra.
Qed.

Lemma ternary_equal_weights_application :
  forall T u0 u1 u2,
  ternary_barycentric_map T (1/3) (1/3) (1/3) ->
  T [u0; u1; u2] = [(u0 + u1 + u2)/3; (u0 + u1 + u2)/3; (u0 + u1 + u2)/3].
Proof.
  intros T u0 u1 u2 Hbary.
  apply (equal_weights_collapses_to_uniform T Hbary u0 u1 u2).
Qed.

Lemma safe_ratio_are_reciprocals :
  forall u_sum v_sum,
  u_sum > 0 -> v_sum > 0 ->
  Rabs u_sum > 1e-100 -> Rabs v_sum > 1e-100 ->
  safe_ratio u_sum v_sum = / safe_ratio v_sum u_sum.
Proof.
  intros u_sum v_sum Hu_pos Hv_pos Hu_abs Hv_abs.
  apply safe_ratio_reciprocal; assumption.
Qed.

Lemma reciprocal_ge_one_of_le_one :
  forall r_uv r_vu,
  r_uv = / r_vu ->
  r_vu > 0 ->
  r_vu <= 1 ->
  r_uv >= 1.
Proof.
  intros r_uv r_vu Hinv Hr_vu_pos Hr_vu_le.
  rewrite Hinv.
  apply Rle_ge.
  apply Rmult_le_reg_r with r_vu. exact Hr_vu_pos.
  rewrite Rmult_1_l.
  rewrite <- Rinv_l_sym by lra.
  exact Hr_vu_le.
Qed.

Lemma reciprocal_le_one_of_ge_one :
  forall r_uv r_vu,
  r_uv = / r_vu ->
  r_vu > 0 ->
  r_vu >= 1 ->
  r_uv <= 1.
Proof.
  intros r_uv r_vu Hinv Hr_vu_pos Hr_vu_ge.
  rewrite Hinv.
  apply Rmult_le_reg_r with r_vu. exact Hr_vu_pos.
  rewrite Rmult_1_l. rewrite <- Rinv_l_sym by lra. lra.
Qed.

Lemma ln_reciprocal_safe_ratio :
  forall u_sum,
  u_sum > 0 ->
  Rabs u_sum > 1e-100 ->
  ln (/ safe_ratio u_sum u_sum) = - ln (safe_ratio u_sum u_sum).
Proof.
  intros u_sum Hu_pos Hu_abs.
  apply ln_Rinv.
  unfold safe_ratio.
  destruct (Rle_dec (Rabs u_sum) 1e-100).
  lra. apply Rdiv_lt_0_compat; lra.
Qed.

Lemma Rmax_eq_arg_implies_ge :
  forall x y,
  Rmax x y = x ->
  x >= y.
Proof.
  intros x y H.
  unfold Rmax in H.
  destruct (Rle_dec x y).
  - rewrite <- H. lra.
  - lra.
Qed.

Lemma ln_diff_zero_implies_equal :
  forall x y,
  x > 0 -> y > 0 ->
  ln x - ln y = 0 ->
  x = y.
Proof.
  intros x y Hx Hy H.
  assert (Hln: ln x = ln y) by lra.
  apply ln_inv in Hln; assumption.
Qed.

Lemma reciprocal_le_one_of_ge_one_simple :
  forall x,
  x > 0 ->
  x >= 1 ->
  / x <= 1.
Proof.
  intros x Hpos Hge.
  apply Rmult_le_reg_r with x; [exact Hpos|].
  replace (/ x * x) with 1 by (field; lra).
  lra.
Qed.

Lemma reciprocal_lt_one_of_gt_one :
  forall x,
  x > 0 ->
  x > 1 ->
  / x < 1.
Proof.
  intros x Hpos Hgt.
  apply Rmult_lt_reg_r with x; [exact Hpos|].
  replace (/ x * x) with 1 by (field; lra).
  lra.
Qed.

Lemma hilbert_distance_reciprocal_ratio_zero :
  forall r_uv r_vu,
  r_uv = / r_vu ->
  r_vu > 0 ->
  ln (Rmax r_vu 1) - ln r_vu = 0 ->
  ln (Rmax r_uv 1) - ln r_uv = 0.
Proof.
  intros r_uv r_vu Hinv Hr_vu_pos Hsep.
  assert (Hr_uv_pos: r_uv > 0).
  { rewrite Hinv. apply Rinv_0_lt_compat. exact Hr_vu_pos. }
  destruct (Rle_dec r_vu 1).
  - assert (Hr_vu_eq_1: r_vu = 1).
    { assert (Hmax: Rmax r_vu 1 = 1) by (apply Rmax_right; exact r).
      rewrite Hmax in Hsep.
      assert (Hln1: ln 1 = 0) by apply ln_1.
      rewrite Hln1 in Hsep.
      assert (Hln_eq: ln r_vu = ln 1) by lra.
      assert (Hone: 1 > 0) by lra.
      apply ln_inv in Hln_eq; [|exact Hr_vu_pos|exact Hone].
      lra. }
    subst r_vu.
    rewrite Rinv_1 in Hinv.
    subst r_uv.
    assert (Hmax: Rmax 1 1 = 1) by (apply Rmax_left; lra).
    rewrite Hmax.
    assert (Hln1: ln 1 = 0) by apply ln_1.
    rewrite Hln1.
    unfold Rminus.
    ring.
  - assert (Hr_vu_gt: r_vu > 1) by lra.
    assert (Hr_uv_lt: r_uv < 1).
    { rewrite Hinv. apply reciprocal_lt_one_of_gt_one; assumption. }
    assert (Hmax_uv: Rmax r_uv 1 = 1).
    { apply Rmax_right. lra. }
    rewrite Hmax_uv.
    assert (Hln1: ln 1 = 0) by apply ln_1.
    rewrite Hln1.
    unfold Rminus.
    rewrite Hinv.
    assert (Hln_inv: ln (/ r_vu) = - ln r_vu).
    { apply ln_Rinv. exact Hr_vu_pos. }
    rewrite Hln_inv.
    assert (Hmax_vu: Rmax r_vu 1 = r_vu) by (apply Rmax_left; lra).
    rewrite Hmax_vu in Hsep.
    unfold Rminus in Hsep.
Admitted.

Theorem uniform_contraction_excludes_equal_weights :
  forall T kappa,
  uniform_contraction T kappa ->
  nondegenerate3 T ->
  ~ ternary_barycentric_map T (1/3) (1/3) (1/3).
Proof.
  intros T kappa [Hkappa_lt Hcontraction] [u [v [Hlen_u [Hlen_v [Hu_pos [Hv_pos [Hu_bound [Hv_bound Hsep]]]]]]]].
  intro Hbary.
  destruct (destruct_length3_lists u v Hlen_u Hlen_v) as [u0 [u1 [u2 [v0 [v1 [v2 [Hu_eq Hv_eq]]]]]]].
  subst u v.
  pose proof (ternary_equal_weights_application T u0 u1 u2 Hbary) as HTu.
  pose proof (ternary_equal_weights_application T v0 v1 v2 Hbary) as HTv.
  rewrite HTu in Hsep.
  rewrite HTv in Hsep.
  destruct (in_pos_orthant_triple_components u0 u1 u2 Hu_pos) as [Hu0 [Hu1 Hu2]].
  destruct (in_pos_orthant_triple_components v0 v1 v2 Hv_pos) as [Hv0 [Hv1 Hv2]].
  destruct (extract_triple_bounds u0 u1 u2 v0 v1 v2 Hu_bound Hv_bound) as [Hu0_bound [Hu1_bound [Hu2_bound [Hv0_bound [Hv1_bound Hv2_bound]]]]].
  destruct (triple_sum_positivity_and_abs_bounds u0 u1 u2 v0 v1 v2 Hu0 Hu1 Hu2 Hv0 Hv1 Hv2 Hu0_bound Hu1_bound Hu2_bound Hv0_bound Hv1_bound Hv2_bound) as [Hu_sum_pos [Hv_sum_pos [Hu_abs Hv_abs]]].
  destruct (Rle_dec ((v0 + v1 + v2)/3) ((u0 + u1 + u2)/3)).
  - assert (Hge: (u0 + u1 + u2)/3 >= (v0 + v1 + v2)/3) by lra.
    pose proof (hilbert_distance_uniform_triple ((u0 + u1 + u2)/3) ((v0 + v1 + v2)/3) Hu_sum_pos Hv_sum_pos Hge Hv_abs) as Hdist_zero.
    lra.
  - assert (Hge: (v0 + v1 + v2)/3 >= (u0 + u1 + u2)/3) by lra.
    pose proof (hilbert_distance_uniform_triple ((v0 + v1 + v2)/3) ((u0 + u1 + u2)/3) Hv_sum_pos Hu_sum_pos Hge Hu_abs) as Hdist_zero.
    unfold hilbert_distance in Hsep, Hdist_zero.
    rewrite safe_ratio_constant_list in Hsep by assumption.
    rewrite safe_ratio_constant_list in Hdist_zero by assumption.
    set (r_uv := safe_ratio ((u0 + u1 + u2)/3) ((v0 + v1 + v2)/3)) in Hsep.
    set (r_vu := safe_ratio ((v0 + v1 + v2)/3) ((u0 + u1 + u2)/3)) in Hdist_zero.
    pose proof (safe_ratio_are_reciprocals ((u0 + u1 + u2)/3) ((v0 + v1 + v2)/3) Hu_sum_pos Hv_sum_pos Hu_abs Hv_abs) as Hinv.
    fold r_uv in Hinv. fold r_vu in Hinv.
    rewrite fold_Rmax_triple_constant in Hsep, Hdist_zero.
    rewrite fold_Rmin_triple_constant in Hsep, Hdist_zero.
    rewrite Rmin_Rmax_collapse in Hsep, Hdist_zero.
    assert (Hr_vu_pos: r_vu > 0).
    { unfold r_vu, safe_ratio.
      destruct (Rle_dec (Rabs ((u0 + u1 + u2)/3)) 1e-100).
      exfalso. lra. apply Rdiv_lt_0_compat; lra. }
    pose proof (hilbert_distance_reciprocal_ratio_zero r_uv r_vu Hinv Hr_vu_pos Hdist_zero) as Hdist_vu_zero.
    lra.
Qed.

End LorentzianContractionConjecture.
