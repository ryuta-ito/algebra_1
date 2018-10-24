Require Export set.

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

Definition gen_rel (X Y : Type) := X -> Y -> Prop.

Definition map_rel {X Y : Type} (R : gen_rel X Y) :=
  forall x, forall y y', R x y -> R x y' -> y = y'.
  (* forall x x', x = x' -> forall y y', R x y -> R x' y' -> y = y'. *)
Arguments map_rel {X Y} R/.

Definition inverse_rel {X Y : Type} (R : gen_rel X Y) (R' : gen_rel Y X) :=
  forall x y, R x y -> R' y x.
Arguments inverse_rel {X Y} R R'/.

Definition eq_relation {X : Type} (R : relation X) :=
  reflexive R /\ symmetric R /\ transitive R.
Arguments eq_relation {X} R /.

Structure eq_R X := {
  eq_r : relation X;
  refl : reflexive eq_r;
  symm : symmetric eq_r;
  trans : transitive eq_r
}.

Definition eq_class {X : Type} (r : eq_R X) x : set X :=
  fun y => eq_r X r x y.
Arguments eq_class {X} r x/.

Theorem x_belongs_x_eq_class : forall {X : Type} (r : eq_R X) x,
  belongs x (eq_class r x).
Proof.
  simpl. intros.
  apply (refl X r).
Qed.

Theorem belongs_y_z_in_eq_class__y_z_is_eq :
  forall {X : Type} (x y z : X) (r : eq_R X),
    belongs y (eq_class r x) ->
    belongs z (eq_class r x) ->
    eq_r X r y z.
Proof.
  simpl. intros.
  apply (symm X r) in H.
  apply (trans X r y x z H H0).
Qed.

Theorem belongs_y_in_x_eq_class__x_eq_class_eq_y_eq_class :
  forall {X : Type} (x y : X) (r : eq_R X),
    belongs y (eq_class r x) ->
    same_set (eq_class r x) (eq_class r y).
Proof.
  simpl. intros.
  split.
  -
    intros.
    apply (symm X r) in H.
    apply (trans X r y x s H H0).
  -
    intros.
    apply (trans X r x y s H H0).
Qed.

Theorem eq_class_not_empty__same :
  forall {X : Type} (x y z : X) (r : eq_R X),
    not_empty (eq_class r x) (eq_class r y) ->
    same_set (eq_class r x) (eq_class r y).
Proof.
  simpl. intros.
  split.
  -
    intros.
    inversion H.
    inversion H1.
    apply (symm X r) in H2.
    apply (trans X r y x0 x H3) in H2.
    apply (trans X r y x s H2 H0).
  -
    intros.
    inversion H.
    inversion H1.
    apply (symm X r) in H3.
    apply (trans X r x x0 y H2) in H3.
    apply (trans X r x y s H3 H0).
Qed.