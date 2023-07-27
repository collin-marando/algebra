Require Import List Decidable ZArith Logic.
Require Import Group.
Require Import Lia.

Include ListNotations.

Section s5.

Variable T : Type.
Variable G : T -> Prop.
Variable op : T -> T -> T.
Hypothesis HG : Group G op.

(* 5.1 *)
(* For singletons, using in_list is overkill,
  and adds bulk to the proof. Instead, use a lambda *)
Goal Group (fun a => a = 1) Nat.mul.
Proof.
  apply group with 1 id;
  intros; subst; auto.
Qed.

(* 5.11 *)
(* Requires knowledge of at least rationals (QArith) *)

(* 5.22 *)
Goal forall (a b : T),
  G a -> (exists b, G b /\ op a b = b) -> a = Ge.
Proof.
  intros a b Ga [x [Gx H]].
  apply (right_cancellation G op) with x; auto.
  - apply Ge_c.
  - rewrite Ge_r; auto.
Qed.