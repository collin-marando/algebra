Require Import Arith.
Require Import List.
Require Import Lia.
Require Import Permutation.
Import ListNotations.

(* Local Imports *)
Require Import Laws.
Require Import Group.

Section basic.

Instance Zmod2_bool : Group (fun _ : bool => True) xorb.
Proof.
  apply group with false id; auto;
  try intros a _;
  try solve [destruct a; simpl; auto].
  - unfold assoc; intros.
    symmetry. apply Bool.xorb_assoc_reverse.
Qed.

End basic.

Section modular.

Import Nat.
Import Nat.Div0.

Fixpoint Zmod (n : nat) : list nat := 
  match n with
  | O => []
  | S n' => Zmod n' ++ [n']
  end.

Theorem Zmod_equiv :
  forall n a : nat, In a (Zmod n) <-> 0 <= a < n.
Proof.
  intros n a.
  split; intros Ha.
  - split.
    + apply Nat.le_0_l.
    + induction n; simpl in *; [contradiction|].
      apply in_app_iff in Ha; inversion Ha.
      * constructor. exact (IHn H).
      * destruct H as [Hn | F]; [subst; auto |contradiction].
  - induction n.
    + lia.
    + simpl.
      destruct Ha as [H0 Ha].
      apply in_app_iff.
      destruct (lt_dec a n); [left|right].
      * auto.
      * simpl. left. lia.
Qed.

Lemma Zmod_length : forall n, length (Zmod n) = n.
Proof.
  induction n; simpl; auto.
  rewrite app_length; simpl.
  lia.
Qed.

Lemma Zmod_NoDup : forall n, NoDup (Zmod n).
Proof.
  induction n; simpl.
  - constructor.
  - apply Permutation_NoDup with ([n] ++ Zmod n).
    + apply Permutation_app_comm.
    + simpl; constructor.
      * rewrite Zmod_equiv. lia.
      * apply IHn.
Qed.

Variable N : nat.
Hypothesis HN : N <> 0.

Definition bounded n := 0 <= n < N.
Definition add a b := (a + b) mod N.

#[refine] Instance ZmodN_G:
  Group bounded add := {
    Ge := 0;
    Ginv n := (N - n) mod N
  }.
Proof.
  all: unfold add, bounded.
  - intros. apply mod_bound_pos; lia.
  - unfold assoc. intros.
    rewrite add_comm, !add_mod_idemp_l by auto.
    rewrite add_comm, add_assoc. auto.
  - lia.
  - intros a H; rewrite Nat.add_0_r.
    apply mod_small. lia.
  - intros a H; simpl (0 + a).
    apply mod_small. lia.
  - intros.
    apply mod_bound_pos; lia.
  - intros.
    rewrite Div0.add_mod_idemp_r by auto.
    rewrite add_sub_assoc.
    + replace (a + N - a) with N by lia.
      apply Div0.mod_same; auto.
    + lia.
  - intros.
    rewrite add_mod_idemp_l by auto.
    replace (N - a + a) with N by lia.
    apply mod_same; auto.
Qed.

Instance ZmodN:
  FiniteGroup bounded add.
Proof.
  apply fgroup with (Zmod N).
  - apply ZmodN_G.
  - apply Zmod_NoDup.  
  - apply Zmod_equiv.
Qed.

Theorem ZmodN_elems : 
  Permutation Gelems (Zmod N).
Proof.
  apply NoDup_Permutation.
  - apply Gnodup.
  - apply Zmod_NoDup.
  - intros.
    eapply iff_trans.
    + apply Gequiv.
    + symmetry.
      apply Zmod_equiv.
Qed.

Theorem ZmodN_order : Gorder = N.
Proof.
  unfold Gorder.
  rewrite <- Zmod_length.
  apply Permutation_length.
  apply ZmodN_elems.
Qed.

End modular.