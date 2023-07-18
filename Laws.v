Section Laws.

Variable T : Type.
Variable op:  T -> T -> T.

Definition comm := forall a b : T, op a b = op b a.
Definition assoc := forall a b c : T, op a (op b c) = op (op a b) c.

End Laws.