From Coq Require Import Ensembles.
From Coq Require Import Arith_base.
From Coq Require Import ZArith.
From Coq Require Import Lia.

Section Demo.

Inductive Nats : Ensemble nat :=
  Nats_defn x : Nats x.

Inductive Evens : Ensemble nat :=
  | Evens_Z : Evens 0
  | Evens_S n : Evens (S (S n)).
 
Theorem Evens_sub_Nats : Included nat Evens Nats.
Proof.
  unfold Included, In.
  intros. constructor.
Qed.

Class CommSet (G : Set) (op: G -> G -> G) := {
  CScomm: forall a b : G, op a b = op b a
}.

Class Group' (G : Set) (op: G -> G -> G) := {
  G'e: G;
  G'comm :> CommSet G op;
  G'ident: forall a : G, op G'e a = a
}.

#[refine] Instance groupNat : Group' nat plus := {G'e := 0}.
Proof.
  all: try constructor; intros; lia.
Qed.

End Demo.

Section Basic_laws.
Variable U : Type.
Variable op : U -> U -> U.

Definition commutative := forall x y : U, op x y = op y x.

Definition associative := forall x y z : U, op x (op y z) = op (op x y) z.

Definition left_neutral (e : U) := forall x : U, op e x = x.

Definition right_neutral (e : U) := forall x : U, op x e = x.

Definition left_inverse (inv : U -> U) (e : U) :=
  forall x : U, op (inv x) x = e.

Definition right_inverse (inv : U -> U) (e : U) :=
  forall x : U, op x (inv x) = e.
Variable D : Ensemble U.

Definition endo_function (f : U -> U) :=
  forall x : U, In U D x -> In U D (f x).

Definition endo_operation (op : U -> U -> U) :=
  forall x y : U, In U D x -> In U D y -> In U D (op x y).
End Basic_laws.
#[export] Hint Unfold endo_function endo_operation commutative associative left_neutral
  right_neutral left_inverse right_inverse : core.

Section Groups.
Variable T : Type.

Class Group (G : Set) (op: G -> G -> G) := {
  Ge: T;
  Ginv: T -> T;
  Gclosed: forall a b : T, G a -> G b -> G (op a b);
  Gassoc: associative T op;
  Ge_c: G Ge;
  Ge_l: forall a : T, G a -> op a Ge = a;
  Ge_r: forall a : T, G a -> op Ge a = a;
  Ginv_c: endo_function T G Ginv;
  Ginv_l: True;
  Ginv_r: True
}.

Theorem Group_nonempty {G} {op} `{Group G op} :
  exists a : T, G a.
Proof.
  exists Ge. apply Ge_c.
Qed.

End Groups.

Instance gnat : Group nat .


Definition nonempty {T : Type} (G : Group) :=
  exists a : T, In G a.

Definition ident {T : Type} (G : Group T) :=
  exists e : T, forall a : T, Op G e a = e /\ Op G a e = e.

Definition closed {T : Type} (G : Ensemble T) (op : T -> T -> T) :=
  forall a b : T, G a -> G b -> G (op a b).

Definition Group {T : Type} (G : Ensemble T) (op : T -> T -> T) := 
  nonempty G /\ ident G op /\ closed G op.
  

  
Theorem G_Nats : Group Nats plus.
Proof.
  unfold Group, nonempty.
  exists 0. constructor.