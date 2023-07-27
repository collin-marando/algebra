Require Import Arith.
Require Import List.
Require Import Lia.
Import ListNotations.

Section Group.

(* Implicit Type  *)
Context {T : Type}.

(* This may become a requirement, see notes below *)
Definition decidable_eq T := 
  forall x y : T, {x = y} + {x <> y}.

Definition in_list (l : list T) : T -> Prop :=
  fun a : T => In a l.

(* Note: The lack of excluded middle in CiC means
  this group definition techinically lacks a feature:
  decidability of element equality. This is a requirement
  for some proofs. The decision on whether or not to
  add this property to the context will depend on
  how many proofs end up requiring it. If it is added,
  this would incur extra cost on proofs of instances. 

  Another decision would be whether it should be added
  to the group definition, or as a context variable in 
  the section (above).

  For now, I leave the group definition as is. If many
  proofs with decidability as a requirement emerge, I may
  decide (heh) to add this property and update the
  subsequent instance proofs. This could be as easy
  as adding decidability for whatever types as a 
  section hypothesis for _auto_ to pick up, keeping
  the proofs virtually the same. This would reflect
  nicely with the requirement as a section variable.
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

Class FiniteGroup G op := fgroup {
  GGroup ::> Group G op;
  Gelems : list T;
  Gorder := length Gelems;
  Gnodup : NoDup Gelems;
  Gequiv : forall a, In a Gelems <-> G a
}.

(* ---------- Group Theorems -----------*)

Section group_theorems.

Variable G : T -> Prop.
Variable op : T -> T -> T.
Hypothesis HG : Group G op.

(* Note: There may be a class worth making where membership
  decidabilty is required as a field, if there are sufficient
  theorems that rely on it.
  Update: This likely coincides with decidability
  on equality (mentioned above) *)
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

(* This proof shows that a Group is a FiniteGroup if
  - Element equality is decidable
  - The membership predicate is defined as
    inclusion in some list (finite)
*)
  Lemma in_list_finite `{dec: decidable_eq T} :
  forall (l : list T) op,
  Group (in_list l) op
    -> FiniteGroup (in_list l) op.
Proof.
  intros.
  apply fgroup with (nodup dec l).
  - assumption.
  - apply NoDup_nodup.
  - intros.
    apply iff_trans with (In a l).
    + apply nodup_In.
    + unfold in_list. reflexivity.
Qed.

End group_theorems.

(* ------ Finite Group Theorems ------- *)
Section finite_group_theorems.

Variable G : T -> Prop.
Variable op : T -> T -> T.
Variable HFG : FiniteGroup G op.

Lemma FG_nonempty : Gorder > 0.
Proof.
  unfold Gorder.
  assert (HIn : In Ge Gelems).
  - rewrite Gequiv. apply Ge_c.
  - destruct Gelems; simpl.
    + inversion HIn.
    + lia.
Qed.

End finite_group_theorems.

End Group.