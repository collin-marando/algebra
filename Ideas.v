Require Import Arith.
Require Import List.
Require Import Lia.
Import ListNotations.

(* Local Imports *)
Require Import Laws.

(* General Properties *)
(* Definition comm {T : Type} (op: T -> T -> T) := forall a b : T, op a b = op b a.
Definition assoc {T : Type} (op: T -> T -> T) := forall a b c : T, op a (op b c) = op (op a b) c.
Definition subset {T : Type} (G H : T -> Prop) := forall x, H x -> G x.
*)

(* Group Definitions *)
Section group.

Variable T : Type.

(* 
  In order to maximize the strength of theorems,
  we can weaken the preconditon by only assuming the group
  requirements that we need for the proof. We can implment
  sets of group properties as subclasses of the Group class. 
  The informal description of a Group divides these properties
  into 4 laws: closure, associativity, identity, and inverses.
*)

Class Group (G : T -> Prop) (op : T -> T -> T) := group  {
  Ge: T;
  Ginv: T -> T;
  Gclosed: forall a b, G a -> G b -> G (op a b);
  Gassoc: forall a b c, G a -> G b -> G c -> op a (op b c) = op (op a b) c;
  Ge_c: G Ge;
  Ge_l: forall a, G a -> op a Ge = a;
  Ge_r: forall a, G a -> op Ge a = a;
  Ginv_c: forall a, G a -> G (Ginv a);
  Ginv_l: forall a, G a -> op a (Ginv a) = Ge;
  Ginv_r: forall a, G a -> op (Ginv a) a = Ge
}.

(* ---------- Group Theorems -----------*)

Variable G : T -> Prop.
Variable op : T -> T -> T.
Hypothesis HG : Group G op.

(* Note: There may be a class worth making where membership
  decidabilty is required as a field, if there are sufficient
  theorems that rely on it *)
Definition elem_dec (a : T) := {G a} + {~ G a}.
Definition membership_dec := forall a, elem_dec a.

(* Note for FiniteGroup, ^this can be reflected with in inclusion
  in the list *)

Lemma uniqueness_of_identity i:
  G i
  -> (forall a, G a -> op a i = a) \/ (forall a, G a -> op i a = a)
  -> i = Ge.
Proof.
  intros Hi [Hi_l | Hi_r].
  - rewrite <- (Ge_r i), Hi_l; auto.
    apply Ge_c.
  - rewrite <- (Ge_l i), Hi_r; auto.
    apply Ge_c.
Qed.

Lemma left_cancellation :
forall a b x, G a -> G b -> G x -> op x a = op x b -> a = b.
Proof.
  intros a b x Ga Gb Gx Heq.
  erewrite <- (Ge_r a Ga), <- (Ge_r b Gb) by auto.
  rewrite <- (Ginv_r x Gx) by auto.
  pose proof (Ginv_c x Gx).
  rewrite <- !Gassoc; auto.
  rewrite Heq. auto.
Qed.

Lemma right_cancellation :
forall a b x, G a -> G b -> G x -> op a x = op b x -> a = b.
Proof.
  intros a b x Ga Gb Gx Heq.
  erewrite <- (Ge_l a Ga), <- (Ge_l b Gb) by auto.
  rewrite <- (Ginv_l x Gx) by auto.
  pose proof (Ginv_c x Gx).
  rewrite !Gassoc; auto.
  rewrite Heq. auto.
Qed.

Lemma uniqueness_of_inverses f:
  forall a, G a 
  -> G (f a)
  -> op a (f a) = Ge \/ op (f a) a = Ge
  -> f a = HG.(Ginv) a.
Proof.
  intros a Ga Gfa [Gf_l | Gf_r].
  - apply left_cancellation with a; try assumption.
    + apply Ginv_c, Ga.
    + rewrite Ginv_l; assumption.
  - apply right_cancellation with a; try assumption.
    + apply Ginv_c, Ga.
    + rewrite Ginv_r; assumption.
Qed.

Lemma inv_involutive : 
  forall x, G x -> Ginv (Ginv x) = x.
Proof.
  autounfold.
  intros x Gx.
  pose proof (Ginv_c x Gx) as Gx'.
  remember (Ginv x) as x'.
  symmetry.
  remember (fun _ : T => x) as f.
  replace x with (f x'); [|rewrite Heqf; auto].
  apply uniqueness_of_inverses; auto;
  rewrite Heqx', Heqf; auto.
  left. apply Ginv_r, Gx.
Qed.

Lemma inv_injective :
  forall a b, G a -> G b -> Ginv a = Ginv b -> a = b.
Proof.
  intros a b Ga Gb Heq.
  apply left_cancellation with (Ginv a); auto.
  - apply Ginv_c, Ga.
  - rewrite Heq at 2.
    rewrite !Ginv_r; auto.
Qed.

(* ------------- Subgroups ------------- *)

(* Subgroup via subset + group *)
Definition subgroup (A : T -> Prop) `(Group A op) := 
  subset G A.
(* This reads weird... _given a group, is subset -> subgroup_
  Should be _given a subset, group -> subgroup_
  Need to figure out how to swap these and still
  equate the definitions below.
*)

(* Subgroup via least requirements *)
Class SubGroup (A : T -> Prop) := sgroup {
  Ssub : forall x, A x -> G x;
  Snon_emp : exists x, A x;
  Sclosed : forall x y, A x -> A y -> A (op x y); 
  Sinv : forall x, A x -> A (Ginv x)
}.

(* Equivalence of the two definitions *)
(* Tip: Display implicit arguments to maintain sanity *)
Theorem subgroup_equiv : forall A HGA,
  SubGroup A <-> subgroup A HGA.
Proof.
  unfold subgroup, subset.
  intros; split; [intro; apply Ssub |].
  intro sgA; split.
  - apply sgA.
  - exists HGA.(Ge). apply Ge_c.
  - apply Gclosed.
  - intros x Ax.
    rewrite <- (uniqueness_of_inverses (HGA.(Ginv))).
    + apply Ginv_c, Ax.
    + apply sgA, Ax.
    + apply sgA, Ginv_c, Ax.
    + left.
      rewrite Ginv_l; auto.
      apply left_cancellation with x.
      * apply sgA, Ge_c.
      * apply Ge_c.
      * apply sgA, Ax.
      * rewrite !Ge_l; auto.
Qed.

(* Finite Groups *)
Section finite.

Class FiniteGroup := fgroup {
  GGroup ::> Group G op;
  Gelems : list T;
  Gorder := length Gelems;
  Gequiv : forall a, List.In a Gelems <-> G a
}.

End finite.

End group.

Check FiniteGroup.
Check Group.

(* ---------------------- Instances ------------------------*)

Section basic.

Instance Zmod2_bool : Group _ (fun _ : bool => True) xorb.
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

Variable N : nat.

Definition bounded n := 0 <= n < N.
Definition add a b := (a + b) mod N.

Hypothesis HN : N <> 0.

#[refine] Instance ZmodN_G : 
  Group _ bounded add := {
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

Fixpoint Zmod (n : nat) : list nat := 
  match n with
  | O => []
  | S n' => Zmod n' ++ [n']
  end.

Theorem mod_list_pred_equiv :
  forall n a : nat, List.In a (Zmod n) <-> 0 <= a < n.
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

Check ZmodN_G.

Definition ZmodN: 
  FiniteGroup nat bounded add.
Proof.
  apply fgroup with (Zmod N).
  - apply ZmodN_G.
  - apply mod_list_pred_equiv.
Qed.

End modular.

(* Goals *)
(*
  ✓ Separate modules/files
  ✓ Eliminate Nat. Nat.Div0. mentions via proper import
  - Group isomorphism
  - Quotient Groups
  - Cardinality
  - Lagrange's Theorem
*)