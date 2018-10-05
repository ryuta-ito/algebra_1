Require Export group.

Definition relation (X : Type) := X -> X -> Prop.

Definition reflexive {X : Type} (R : relation X) :=
  forall x : X, R x x.
Arguments reflexive {X} R /.

Definition symmetric {X : Type} (R : relation X) :=
  forall x y: X, R x y -> R y x.
Arguments symmetric {X} R /.

Definition transitive {X : Type} (R : relation X) :=
  forall x y z : X,
    R x y -> R y z -> R x z.
Arguments transitive {X} R /.

Definition eq_relation {X : Type} (R : relation X) :=
  reflexive R /\ symmetric R /\ transitive R.
Arguments eq_relation {X} R /.

Definition left_coset_rel {M : Type} (H G : group M) : relation M :=
  fun x => fun y =>
    subgroup H G -> belongs (bin M G (inverse M G x) y) (cset M H).
(* Arguments left_coset_rel {M} H G /. *)

Theorem left_coset_rel_is_eq_relation : forall {M : Type} (H G : group M), eq_relation (left_coset_rel H G).
Proof.
  simpl. intros.
  unfold left_coset_rel.
  split.
  -
    intros.
    rewrite (invL M G x).
    apply (subgroup_has_id H G H0).
  -
    split.
    +
      intros.
      apply H0 in H1 as H2.
      apply (inv_belongs M H (bin M G (inverse M G x) y)) in H2.
      rewrite (inverse_distributive G (inverse M G x) y) in H2.
      Check inverse_distributive G.
      inversion H1.
      apply H3 in H2.
      apply (inv_belongs M G (bin M G (inverse M G x) y)) in H2.


