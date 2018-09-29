Require Export set.

Structure group M := {
  cset : set M;
  id : M;
  bin : M -> M -> M;
  inverse : M -> M;
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
