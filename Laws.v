Section Laws.

Context {T  : Type}.
Variable un : T -> T.
Variable op :  T -> T -> T.
Variable G H : T -> Prop.

(* Unary Operator Laws *)
Definition constant := exists x, forall a, un a = x.
Definition involutive := forall a, un (un a) = a.

(* Binary Operator Laws *)
Definition comm := forall a b, op a b = op b a.
Definition assoc := forall a b c, op a (op b c) = op (op a b) c.

(* Predicate Laws *)
Definition endo_op := forall a b, G a -> G b -> G (op a b).

Definition subset (G H : T -> Prop) := forall x, H x -> G x.

End Laws.

#[export] Hint Unfold all : core.