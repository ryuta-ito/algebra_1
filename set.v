Definition set (M : Type) := M -> Prop.
Definition belongs {M : Type} (x : M) (P : set M) : Prop := P x.
Arguments belongs {M} x P /.

Axiom belongs__exists : forall {M : Type} (x : M) (P : set M),
  belongs x P -> exists y, belongs y P /\ x = y.

Definition subset {M : Type} (S T : set M) :=
  forall s, belongs s S -> belongs s T.
Arguments subset {M} S T /.

Definition same_set {M : Type} (S T : set M) :=
  subset S T /\ subset T S.
Arguments same_set {M} S T /.

Definition not_empty {M : Type} (S T : set M) :=
  exists x, belongs x S /\ belongs x T.
Arguments not_empty {M} S T /.

Definition map {M M' : Type} f (A : set M) (B : set M') :=
  forall x, belongs x A -> belongs (f x) B.
Arguments map {M M'} f A B /.

Definition injection {M M' : Type} f (A : set M) (B : set M') :=
  map f A B -> forall x y,
    f x = f y -> x = y.
Arguments injection {M M'} f A B /.
