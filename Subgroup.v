Require Import Group.


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