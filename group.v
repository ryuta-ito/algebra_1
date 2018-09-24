Require Export set.

Definition id {M : Type} (S : set M) (id : M) (bin : M -> M -> M) :=
  forall s, belongs s S -> bin s id = s /\ bin id s = s.

Axiom id_belongs : forall {M : Type} (S : set M) (id_ : M) bin,
  id S id_ bin -> belongs id_ S.

Definition identity {M : Type} (S : set M) (bin : M -> M -> M) :=
  exists e, id S e bin.

Definition inverse {M : Type} (S : set M) (s s' : M) (bin : M -> M -> M) :=
    belongs s' S ->
    id S (bin s s') bin /\ id S (bin s' s) bin.

Definition inversible {M : Type} (S : set M) (bin : M -> M -> M) : Prop :=
  forall s, belongs s S -> exists s', inverse S s s' bin.

Definition associative {M : Type} (S : set M) (bin : M -> M -> M) : Prop :=
  forall a b c,
    belongs a S ->
    belongs b S ->
    belongs c S ->
    bin a (bin b c) = bin (bin a b) c.

Definition entire_property {M : Type} (S : set M) (bin : M -> M -> M) : Prop :=
  forall x y, belongs x S -> belongs y S -> belongs (bin x y) S.

Definition magma {M : Type} (S : set M) bin :=
  entire_property S bin.

Definition semigroup {M : Type} (S : set M) bin :=
  magma S bin /\ associative S bin.

Definition monoid {M : Type} (S : set M) bin :=
  semigroup S bin /\ identity S bin.

Axiom monoid_has_id : forall {M:Type} (S : set M) bin,
  monoid S bin -> exists id_S, belongs id_S S /\ id S id_S bin.

Definition group {M : Type} (S : set M) bin :=
  monoid S bin /\ inversible S bin.

Lemma group_has_id : forall {M:Type} (S : set M) bin,
  group S bin -> exists id_S, belongs id_S S /\ id S id_S bin.
Proof.
  intros.
  unfold group in H.
  inversion H.
  apply (monoid_has_id S bin H0).
Qed.

Axiom group_inverse_belongs : forall {M:Type} (S : set M) bin,
  forall g g', group S bin -> inverse S g g' bin -> belongs g S /\ belongs g' S.

Definition subgroup {M : Type} (H G : set M) bin :=
  subset H G /\ group H bin /\ group G bin.

Definition homomorphism {M_1 M_2 : Type} (G_1 : set M_1) bin_1 (G_2 : set M_2) bin_2 (f : M_1 -> M_2) :=
 group G_1 bin_1 -> group G_2 bin_2 -> map f G_1 G_2 ->
 forall x y,
   belongs x G_1 -> belongs y G_1 ->
   f (bin_1 x y) = bin_2 (f x) (f y).

Lemma group_has_g_inverse_g' : forall {M : Type} (G : set M) bin g,
  belongs g G -> group G bin -> exists g', belongs g' G /\ inverse G g g' bin.
Proof.
  intros.
  assert (H1:=H0).
  unfold group in H0.
  inversion H0 as [_ H2].
  unfold inversible in H2.
  specialize H2 with g.
  apply H2 in H.
  inversion H as [g'].
  exists g'.
  split.
  -
    apply (group_inverse_belongs G bin g g' H1) in H3.
    inversion H3.
    assumption.
  -
    assumption.
Qed.

Lemma group_has_assoc : forall {M : Type} (G : set M) bin,
  group G bin -> associative G bin.
Proof.
  intros.
  unfold group,monoid,semigroup in H.
  inversion H as [[[_ H0] _] _].
  assumption.
Qed.

Lemma group_has_entire : forall {M : Type} (G : set M) bin,
  group G bin -> entire_property G bin.
Proof.
  intros.
  unfold group,monoid,semigroup,magma in H.
  inversion H as [[[H0 _] _] _].
  assumption.
Qed.

Lemma specific_inverse_to_id : forall {M : Type} (G : set M) bin g g' id_G,
  group G bin -> id G id_G bin -> inverse G g g' bin -> bin g g' = id_G /\ bin g' g = id_G.
Proof.
  intros.
  apply (id_belongs G id_G bin) in H0 as H2.
  apply (group_inverse_belongs G bin g g' H) in H1 as H3.
  inversion H3.
  unfold inverse,id in H1.
  apply H1 in H5 as H6.
  inversion H6.
  unfold id in H0.
  apply (group_has_entire G bin) in H as H9.
  unfold entire_property in H9.
  split.
  -
    apply (H7 id_G) in H2 as H10.
    inversion H10.
    apply (H9 g g' H4) in H5 as H13.
    apply (H0 (bin g g')) in H13 as H14.
    inversion H14.
    rewrite H15 in H12.
    assumption.
  -
    apply (H8 id_G) in H2 as H10.
    inversion H10.
    apply (H9 g' g H5) in H4 as H13.
    apply (H0 (bin g' g)) in H13 as H14.
    inversion H14.
    rewrite H15 in H12.
    assumption.
Qed.
