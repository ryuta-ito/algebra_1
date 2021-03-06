Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.

Definition set (M : Type) := M -> Prop.
Definition belongs (M : Type) (x : M) (P : set M) : Prop := P x.
Arguments belongs M x P /.

Notation "x \in P" := (belongs x P) (at level 11).

Axiom belongs__exists : forall (M : Type) (x : M) (P : set M),
  x \in P -> exists y, y \in P /\ x = y.

Definition subset (M : Type) (S T : set M) :=
  forall s, s \in S -> s \in T.
Arguments subset M S T /.

Notation "X \subset Y" := (subset X Y) (at level 11).

Definition same_set (M : Type) (S T : set M) :=
  S \subset T /\ T \subset S.
Arguments same_set M S T /.

Axiom same_set__eq : forall (M : Type) (S T : set M),
  same_set S T <-> S = T.

Definition not_empty (M : Type) (S T : set M) :=
  exists x, x \in S /\ x \in T.
Arguments not_empty M S T /.

Definition map (M M' : Type) f (A : set M) (B : set M') :=
  forall x, x \in A -> (f x) \in B.
Arguments map M M' f A B /.

Definition injection (M M' : Type) f (A : set M) (B : set M') :=
  map f A B -> forall x y,
    f x = f y -> x = y.
Arguments injection M M' f A B /.

Definition surjection (M M' : Type) f (A : set M) (B : set M') :=
  map f A B ->
    forall y, y \in B ->
      exists x, x \in A -> f x = y.
Arguments surjection M M' f A B /.

Definition bijection (M M' : Type) f (A : set M) (B : set M') :=
  injection f A B /\ surjection f A B.
Arguments bijection M M' f A B /.

Definition same_order (M M' : Type) (A : set M) (B : set M') :=
  exists f, bijection f A B.
Arguments same_order M M' A B /.
