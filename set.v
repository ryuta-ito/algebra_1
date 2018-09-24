Definition set (M : Type) := M -> Prop.
Definition belongs {M : Type} (x : M) (P : set M) : Prop := P x.
Definition subset {M : Type} (S T : set M) :=
  forall s, belongs s S -> belongs s T.

Definition map {M_A M_B : Type} f (A : set M_A) (B : set M_B) :=
  forall x, belongs x A -> belongs (f x) B.

Definition injection {M : Type} f (A B : set M) :=
  map f A B -> forall x y,
    belongs x A ->
    belongs y A ->
    f x = f y -> x = y.
