Definition set (M : Type) := M -> Prop.
Definition belongs {M : Type} (x : M) (P : set M) : Prop := P x.
Arguments belongs {M} x P /.

Definition subset {M : Type} (S T : set M) :=
  forall s, belongs s S -> belongs s T.

Definition map {M M' : Type} f (A : set M) (B : set M') :=
  forall x, belongs x A -> belongs (f x) B.
Arguments map {M M'} f A B /.

Definition injection {M M' : Type} f (A : set M) (B : set M') :=
  map f A B -> forall x y,
    f x = f y -> x = y.
Arguments injection {M M'} f A B /.
