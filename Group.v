Require Import Arith.
Require Import List.
Require Import Lia.
Import ListNotations.

Section Group.

(* Implicit Type  *)
Context {T : Type}.

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


(* Finite Groups *)
Section finite.

Class FiniteGroup := fgroup {
  GGroup ::> Group G op;
  Gelems : list T;
  Gorder := length Gelems;
  Gequiv : forall a, List.In a Gelems <-> G a
}.

End finite.

End Group.