Require Export set.

Structure group M := {
  cset : set M;
  id : M;
  id_belongs : belongs id cset;
  bin : M -> M -> M;
  inverse : M -> M;
  inv_belongs : forall g, belongs g cset -> belongs (inverse g) cset;
  entire : forall x y, belongs x cset -> belongs y cset -> belongs (bin x y) cset;
  assoc : forall x y z, bin x (bin y z) = bin (bin x y) z;
  idR : forall g, bin g id = g;
  idL : forall g, bin id g = g;
  invR : forall g, bin g (inverse g) = id;
  invL : forall g, bin (inverse g) g = id
}.

Structure hom M G M' G' := {
  hom_f : M -> M';
  hom_is_map : map hom_f (cset M G) (cset M' G');
  hom_law : forall x y, hom_f (bin M G x y) = bin M' G' (hom_f x) (hom_f y)
}.

Lemma both_sides_L : forall {M : Type} (bin : M -> M -> M) (x y z : M),
  x = y -> bin z x = bin z y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma both_sides_R : forall {M : Type} (bin : M -> M -> M) (x y z : M),
  x = y -> bin x z = bin y z.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma id_inverse_eq_id : forall {M : Type} (G : group M),
  inverse M G (id M G) = id M G.
Proof.
  intros.
  assert (H := idR M G (id M G)).
  apply (both_sides_L (bin M G))
    with (z := (inverse M G (id M G))) in H.
  rewrite (invL M G (id M G)) in H.
  rewrite (assoc M G (inverse M G (id M G)) (id M G) (id M G)) in H.
  rewrite (idR M G (inverse M G (id M G))) in H.
  rewrite (idR M G (inverse M G (id M G))) in H.
  assumption.
Qed.

Lemma inverse_eq : forall {M : Type} (G : group M) g,
  inverse M G (inverse M G g) = g.
Proof.
  intros.
  assert (bin M G (inverse M G g) (inverse M G (inverse M G g)) = id M G)
    by (rewrite invR; reflexivity).
  apply (both_sides_L (bin M G)) with (z := g) in H.
  rewrite assoc in H.
  rewrite invR in H.
  rewrite idL in H.
  rewrite idR in H.
  assumption.
Qed.

Lemma inverse_distributive : forall {M : Type} (G : group M) g g',
  inverse M G (bin M G g g') = bin M G (inverse M G g') (inverse M G g).
Proof.
  intros.
  assert (bin M G g' (inverse M G g') = id M G) by (apply (invR M G g')).
  apply (both_sides_L (bin M G)) with (z := g) in H.
  apply (both_sides_R (bin M G)) with (z := (inverse M G g)) in H.
  rewrite (idR M G g) in H.
  rewrite (invR M G g) in H.
  rewrite <- (assoc M G g (bin M G g' (inverse M G g')) (inverse M G g)) in H.
  rewrite <- (assoc M G g' (inverse M G g') (inverse M G g)) in H.
  rewrite (assoc M G g g' (bin M G (inverse M G g') (inverse M G g))) in H.
  apply (both_sides_L (bin M G)) with (z := inverse M G (bin M G g g')) in H.
  rewrite (idR M G (inverse M G (bin M G g g'))) in H.
  rewrite (assoc M G (inverse M G (bin M G g g')) (bin M G g g') (bin M G (inverse M G g') (inverse M G g))) in H.
  rewrite (invL M G (bin M G g g')) in H.
  rewrite (idL M G (bin M G (inverse M G g') (inverse M G g))) in H.
  symmetry.
  assumption.
Qed.

Definition subgroup {M : Type} (H G : group M) :=
  (forall g, belongs g (cset M H) -> belongs g (cset M G)) /\
  forall g g', belongs g (cset M H) -> belongs g' (cset M H) -> bin M H g g' = bin M G g g'.
Arguments subgroup {M} H G /.

Theorem subgroup_id_eq : forall {M : Type} (H G : group M),
  subgroup H G -> id M H = id M G.
Proof.
  simpl. intros.
  inversion H0.
  assert (bin M G (id M H) (id M H) = id M H).
  -
    rewrite <- (H2 (id M H) (id M H) (id_belongs M H) (id_belongs M H)).
    apply (idL M H (id M H)).
  -
    apply (both_sides_L (bin M G)) with (z := inverse M G (id M H)) in H3.
    rewrite (invL M G (id M H)) in H3.
    rewrite (assoc M G (inverse M G (id M H)) (id M H) (id M H)) in H3.
    rewrite (invL M G (id M H)) in H3.
    rewrite (idL M G (id M H)) in H3.
    assumption.
Qed.

Theorem subgroup_has_id : forall {M : Type} (H G : group M),
  subgroup H G -> belongs (id M G) (cset M H).
Proof.
  intros.
  rewrite <- (subgroup_id_eq H G H0).
  apply (id_belongs M H).
Qed.

Theorem subgroup_inverse_eq : forall {M : Type} (H G : group M) x,
  subgroup H G ->
  belongs x (cset M H) ->
  inverse M H x = inverse M G x.
Proof.
  intros.
  inversion H0.
  assert (bin M H x (inverse M H x) = bin M G x (inverse M H x))
    by (apply (H3 x (inverse M H x) H1 (inv_belongs M H x H1))).
  rewrite (invR M H x) in H4.
  rewrite (subgroup_id_eq H G H0) in H4.
  apply (both_sides_L (bin M G)) with (z := inverse M G x) in H4.
  rewrite (idR M G (inverse M G x)) in H4.
  rewrite (assoc M G) in H4.
  rewrite (invL M G x) in H4.
  rewrite (idL M G) in H4.
  symmetry.
  assumption.
Qed.
