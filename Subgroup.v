Require Import Group.
Require Import Laws.

Include Group.
Section Subgroup.

(* Implicit Type *)
Context {T : Type}.

Variable G H : T -> Prop.
Variable op : T -> T -> T.
Hypothesis GG : Group G op.

(* Subgroup via subset + group *)
Inductive subgroup : Prop :=
  | SGroup : subset G H -> Group H op -> subgroup.

(* Subgroup via least requirements *)
Class Subgroup : Prop := sgroup { 
  Ssub : forall x, H x -> G x;
  Snon_emp : exists x, H x;
  Sclosed : forall x y, H x -> H y -> H (op x y); 
  Sinv : forall x, H x -> H (Ginv x)
}.

Theorem subgroup_Subgroup : subgroup -> Subgroup.
Proof.
  intros [sgA GH].
  unfold subset in *.
  split.
  - apply sgA.
  - exists GH.(Ge). apply Ge_c.
  - apply Gclosed.
  - intros x Hx.
    rewrite <- (uniqueness_of_inverses _ _ _ (GH.(Ginv))).
    + apply Ginv_c, Hx.
    + apply sgA, Hx.
    + apply sgA, Ginv_c, Hx.
    + left.
      rewrite Ginv_l; auto.
      apply (left_cancellation _ _ GG _ _ x).
      * apply sgA, Ge_c.
      * apply Ge_c.
      * apply sgA, Hx.
      * rewrite !Ge_l; auto.
Qed.

Theorem Subgroup_subgroup : Subgroup -> subgroup.
Proof.
  intros SGA.
  split.
  - intro x. apply Ssub.
  - apply group with Ge Ginv.
    + apply Sclosed.
    + intros a b c Ha Hb Hc.
      apply Gassoc; apply Ssub; auto.
    + pose proof Snon_emp as [x Hx].
      rewrite <- (Ginv_l x); [|apply Ssub, Hx].
      apply Sclosed; auto.
      apply Sinv; auto.
    + intros a Ha.
      apply Ge_l, Ssub, Ha.
    + intros a Ha.
      apply Ge_r, Ssub, Ha.
    + apply Sinv.
    + intros a Ha.
      apply Ginv_l, Ssub, Ha.
    + intros a Ha.
      apply Ginv_r, Ssub, Ha.
Qed.

(* Equivalence of the two definitions *)
(* Tip: Display implicit arguments to maintain sanity *)
Theorem subgroup_equiv : 
  Subgroup <-> subgroup.
Proof.
  intros; split.
  - apply Subgroup_subgroup.
  - apply subgroup_Subgroup.
Qed.

End Subgroup.