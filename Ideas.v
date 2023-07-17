Require Import Arith.
Require Import List.
Require Import Lia.
Import ListNotations.

(* General Properties *)
Definition comm {T : Type} (op: T -> T -> T) := forall a b : T, op a b = op b a.
Definition assoc {T : Type} (op: T -> T -> T) := forall a b c : T, op a (op b c) = op (op a b) c.

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

(*
Class closed (G : T -> Prop) (op : T -> T -> T) := {
  Gclos: forall a b, G a -> G b -> G (op a b);
}.

Class associative (G : T -> Prop) (op : T -> T -> T) := {
  Gassoc: assoc op;
}.

Class identity (G : T -> Prop) (op : T -> T -> T) := {
  Ge : T;
  Ge_c: G Ge;
  Ge_l: forall a, G a -> op a Ge = a;
  Ge_r: forall a, G a -> op Ge a = a;
}.

Class inverse (G : T -> Prop) (op : T -> T -> T) := {
  Ginv : T -> T;
  Gidentity :> identity G op;
  Ginv_c: forall a, G a -> G (Ginv a);
  Ginv_l: forall a, G a -> op a (Ginv a) = Ge;
  Ginv_r: forall a, G a -> op (Ginv a) a = Ge;
}.

Class Group (G : T -> Prop) (op : T -> T -> T) := {
  Ginverse :> inverse G op;
  Gclosed :> closed G op;
  Gassociative :> associative G op;
}.

(* Note that inverse depends on identity. Therefore,
  _inverse_ implements _identity_, and it should not
  be repeated in the definition of the _Group_ class.
  There is weaker definition of the law of inverses called divisibility. This could have been
  used to keep the subclasses disjoint, but divisibility serves
  little use as a distinct law in group theory.
*)

*)

Class Group (G : T -> Prop) (op : T -> T -> T) := {
  Ge: T;
  Ginv: T -> T;
  Gclosed: forall a b, G a -> G b -> G (op a b);
  Gassoc: assoc op;
  Ge_c: G Ge;
  Ge_l: forall a, G a -> op a Ge = a;
  Ge_r: forall a, G a -> op Ge a = a;
  Ginv_c: forall a, G a -> G (Ginv a);
  Ginv_l: forall a, G a -> op a (Ginv a) = Ge;
  Ginv_r: forall a, G a -> op (Ginv a) a = Ge
}.

Check Group.

(* ---------- Group Theorems -----------*)

(* Note: This proof only actually requires right or left id *)
Lemma uniqueness_of_identity G op i `{Group G op} :
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

Lemma left_cancellation G op `{Group G op} :
forall a b x, G a -> G b -> G x -> op x a = op x b -> a = b.
Proof.
  intros a b x Ga Gb Gx Heq.
  inversion H.
  erewrite <- (Ge_r a Ga), <- (Ge_r b Gb) by auto.
  rewrite <- (Ginv_r x Gx) by auto.
  rewrite <- !Gassoc.
  rewrite Heq. auto.
Qed.

(* Note: This proof only actually requires right or left inv *)
Lemma uniqueness_of_inverses G op f `{HG : Group G op}:
  forall a, G a 
  -> G (f a)
  -> op a (f a) = Ge
  -> op (f a) a = Ge
  -> f a = HG.(Ginv) a.
Proof.
  intros a Ga Gfa Gf_l Gf_r.
  pose proof (left_cancellation G op) as H.
  apply H with a; try assumption.
  - apply Ginv_c, Ga.
  - rewrite Ginv_l; assumption.
Qed.

Lemma inv_involutive G op `{Group G op} :
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
  - apply Ginv_r, Gx.
  - apply Ginv_l, Gx.
Qed.

Lemma inv_cancel G op `{Group G op} :
  forall a b, G a -> G b -> Ginv a = Ginv b -> a = b.
Proof.
  intros a b Ga Gb Heq.
  eapply (left_cancellation G op a b (Ginv a)); auto.
  - apply Ginv_c, Ga.
  - 
Admitted.

(* Not sure if this is useful or even provable *)
Lemma inv_conv G op `{Group G op} :
  forall x, G (Ginv x) -> G x.
Proof.
  intros x GGinv.
  pose proof (inv_involutive G op _ GGinv) as Hii.

  apply f_equal in Hii.
  specialize (Hii (Ginv x)).
  rewrite <- 
  rewrite 


(* ------------- Subgroups ------------- *)

(* Subgroup via group + subset *)
Definition subgroup A B op `(GA: Group A op) `{Group B op} :=
  forall x, A x -> B x.

(* Subgroup via least requirements *)
Class SubGroup (A B : T -> Prop) op `{Group B op} := {
  Ssub : forall x, A x -> B x;
  Snon_emp : exists x, A x;
  Sclosed : forall x y, A x -> A y -> A (op x y); 
  Sinv : forall x, A x -> A (Ginv x)
}.

(* Equivalence of the two definitions *)
Theorem subgroup_equiv : forall A B op `{GB: Group B op},
  (exists P, subgroup A B op P) <-> SubGroup A B op.
Proof.
  intros; split; [intro sgA | intro SGA].
  - destruct sgA as [GA sgA].
    unfold subgroup in sgA.
    split.
    + apply sgA.
    + exists GA.(Ge). apply Ge_c.
    + apply Gclosed.
    + intros.
      assert (forall y, A y -> GA.(Ginv) y = GB.(Ginv) y).
      {
        pose proof (Ginv_c _ H). 
      }

      unfold Ginv.
      f_equal.
      destruct GB.
      destruct GA.
      assert Gi
      pose proof Ginv.
      apply H0.
      auto.
      rewrite Ginv_l.    


(* Finite Groups *)
Section finite.

Class FiniteGroup `{Group} := {
  Gelems : list T;
  Gequiv : forall a, List.In a Gelems <-> G a
}.

End finite.
End group.

Section modular.

Variable N : nat.
Hypothesis HN : N <> 0.

Definition PG n := 0 <= n < N.
Definition add a b := (a + b) mod N.

#[refine] Local Instance ZmodN_G : 
  Group _ PG add := {
    Ge := 0;
    Ginv n := (N - n) mod N
  }.
Proof.
  all: unfold add, PG.
  - intros. apply Nat.mod_bound_pos; lia.
  - unfold assoc. intros.
    rewrite Nat.add_comm, !Nat.add_mod_idemp_l by auto.
    rewrite Nat.add_comm, Nat.add_assoc. auto.
  - lia.
  - intros a H; rewrite Nat.add_0_r.
    apply Nat.mod_small. lia.
  - intros a H; simpl (0 + a).
    apply Nat.mod_small. lia.
  - intros.
    apply Nat.mod_bound_pos; lia.
  - intros.
    rewrite Nat.add_mod_idemp_r by auto.
    rewrite Nat.add_sub_assoc.
    + replace (a + N - a) with N by lia.
      apply Nat.mod_same; auto.
    + lia.
  - intros.
    rewrite Nat.add_mod_idemp_l by auto.
    replace (N - a + a) with N by lia.
    apply Nat.mod_same; auto.
Qed.

Fixpoint Zmod (n : nat) : list nat := 
  match n with
  | O => []
  | S n' => Zmod n' ++ [n']
  end.

Theorem mod_list_pred_eqv :
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

Local Instance ZmodN: 
  FiniteGroup nat PG add.
Proof.
  econstructor. eapply mod_list_pred_eqv.
Qed.