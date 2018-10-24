Require Export group.
Require Export relation.

Definition left_coset_rel {M : Type} (H G : group M) : relation M :=
  fun x => fun y =>
    subgroup H G -> belongs (bin M G (inverse M G x) y) (cset M H).

Definition right_coset_rel {M : Type} (H G : group M) : relation M :=
  fun x => fun y =>
    subgroup H G -> belongs (bin M G y (inverse M G x)) (cset M H).

Definition left_coset {M : Type} (H G : group M) (x : M) : set M :=
  fun y => left_coset_rel H G x y.

Definition left_coset' {M : Type} (H G : group M) (x : M) : set M :=
  fun y => exists h, belongs h (cset M H) /\ y = bin M G x h.

Lemma g_in_G_h_in_H__gh_in_gH : forall {M : Type} (H G : group M) h g,
  belongs h (cset M H) -> belongs g (cset M G) ->
  belongs (bin M G g h) (left_coset' H G g).
Proof.
  intros.
  unfold left_coset'.
  simpl.
  exists h.
  split.
  -
    assumption.
  -
    reflexivity.
Qed.

Definition right_coset {M : Type} (H G : group M) (x : M) : set M :=
  fun y => right_coset_rel H G x y.

Definition right_coset' {M : Type} (H G : group M) (x : M) : set M :=
  fun y => exists h, belongs h (cset M H) /\ y = bin M G h x.

Lemma g_in_G_h_in_H__gh_in_Hg : forall {M : Type} (H G : group M) h g,
  belongs h (cset M H) -> belongs g (cset M G) ->
  belongs (bin M G h g) (right_coset' H G g).
Proof.
  intros.
  unfold right_coset'.
  simpl.
  exists h.
  split.
  -
    assumption.
  -
    reflexivity.
Qed.

Theorem left_coset_eq_left_coset' : forall {M : Type} (H G : group M) x,
  subgroup H G -> same_set (left_coset H G x) (left_coset' H G x).
Proof.
  intros.
  unfold same_set.
  split.
  -
    simpl.
    unfold left_coset,left_coset',left_coset_rel.
    intros.
    apply H1 in H0.
    simpl in H0.
    apply belongs__exists in H0.
    inversion H0 as [h].
    inversion H2.
    exists h.
    split.
    +
      assumption.
    +
      rewrite <- H4.
      rewrite assoc.
      rewrite invR.
      rewrite idL.
      reflexivity.
  -
    simpl.
    unfold left_coset,left_coset',left_coset_rel.
    intros.
    inversion H1 as [h].
    inversion H3.
    rewrite H5.
    rewrite assoc.
    rewrite invL.
    rewrite idL.
    assumption.
Qed.

Theorem right_coset_eq_right_coset' : forall {M : Type} (H G : group M) x,
  subgroup H G -> same_set (right_coset H G x) (right_coset' H G x).
Proof.
  intros.
  unfold same_set.
  split.
  -
    simpl.
    unfold right_coset,right_coset',right_coset_rel.
    intros.
    apply H1 in H0.
    simpl in H0.
    apply belongs__exists in H0.
    inversion H0 as [h].
    inversion H2.
    exists h.
    split.
    +
      assumption.
    +
      rewrite <- H4.
      rewrite <- assoc.
      rewrite invL.
      rewrite idR.
      reflexivity.
  -
    simpl.
    unfold right_coset,right_coset',right_coset_rel.
    intros.
    inversion H1 as [h].
    inversion H3.
    rewrite H5.
    rewrite <- assoc.
    rewrite invR.
    rewrite idR.
    assumption.
Qed.

Theorem l_coset_rel_reflexive : forall {M : Type} (H G : group M), reflexive (left_coset_rel H G).
Proof.
  simpl.
  intros.
  unfold left_coset_rel.
  intros.
  rewrite (invL M G x).
  apply (subgroup_has_id H G H0).
Qed.

Theorem r_coset_rel_reflexive : forall {M : Type} (H G : group M), reflexive (right_coset_rel H G).
Proof.
  simpl.
  intros.
  unfold right_coset_rel.
  intros.
  rewrite (invR M G x).
  apply (subgroup_has_id H G H0).
Qed.

Theorem l_coset_rel_symmetric : forall {M : Type} (H G : group M), symmetric (left_coset_rel H G).
Proof.
  simpl.
  unfold left_coset_rel.
  intros.
  apply H0 in H1 as H2.
  apply (inv_belongs M H (bin M G (inverse M G x) y)) in H2.
  apply (inv_belongs M H (inverse M H (bin M G (inverse M G x) y)))
    in H2 as H3.
  rewrite inverse_eq in H3.
  rewrite (subgroup_inverse_eq H G (bin M G (inverse M G x) y) H1 H3) in H2.
  rewrite (inverse_distributive G (inverse M G x) y) in H2.
  rewrite inverse_eq in H2.
  assumption.
Qed.

Theorem r_coset_rel_symmetric : forall {M : Type} (H G : group M), symmetric (right_coset_rel H G).
Proof.
  simpl.
  unfold right_coset_rel.
  intros.
  apply H0 in H1 as H2.
  apply (inv_belongs M H (bin M G y (inverse M G x))) in H2.
  apply (inv_belongs M H (inverse M H (bin M G y (inverse M G x))))
    in H2 as H3.
  rewrite inverse_eq in H3.
  rewrite (subgroup_inverse_eq H G (bin M G y (inverse M G x)) H1 H3) in H2.
  rewrite (inverse_distributive G y (inverse M G x)) in H2.
  rewrite inverse_eq in H2.
  assumption.
Qed.

Theorem l_coset_rel_transitive : forall {M : Type} (H G : group M), transitive (left_coset_rel H G).
Proof.
  simpl.
  unfold left_coset_rel.
  intros.
  apply H0 in H2 as H3.
  apply H1 in H2 as H4.
  inversion H2.
  apply (entire M H (bin M G (inverse M G x) y) (bin M G (inverse M G y) z) H3) in  H4 as H7.
  rewrite (H6 (bin M G (inverse M G x) y) (bin M G (inverse M G y) z) H3 H4) in H7.
  rewrite <- assoc in H7.
  replace (bin M G y (bin M G (inverse M G y) z))
    with (bin M G (bin M G y (inverse M G y)) z)
    in H7
    by (rewrite assoc; reflexivity).
  rewrite invR in H7.
  rewrite idL in H7.
  assumption.
Qed.

Theorem r_coset_rel_transitive : forall {M : Type} (H G : group M), transitive (right_coset_rel H G).
Proof.
  simpl.
  unfold right_coset_rel.
  intros.
  apply H0 in H2 as H3.
  apply H1 in H2 as H4.
  inversion H2.
  apply (entire M H (bin M G z (inverse M G y)) (bin M G y (inverse M G x)) H4) in H3 as H7.
  rewrite (H6 (bin M G z (inverse M G y)) (bin M G y (inverse M G x)) H4 H3) in H7.
  rewrite <- assoc in H7.
  replace (bin M G (inverse M G y) (bin M G y (inverse M G x)))
    with (bin M G (bin M G (inverse M G y) y) (inverse M G x))
    in H7
    by (rewrite assoc; reflexivity).
  rewrite invL in H7.
  rewrite idL in H7.
  assumption.
Qed.

Definition l_coset_eq_R {M : Type} (H G : group M) : eq_R M :=
  Build_eq_R M (left_coset_rel H G)
               (l_coset_rel_reflexive H G)
               (l_coset_rel_symmetric H G)
               (l_coset_rel_transitive H G).

Definition r_coset_eq_R {M : Type} (H G : group M) : eq_R M :=
  Build_eq_R M (right_coset_rel H G)
               (r_coset_rel_reflexive H G)
               (r_coset_rel_symmetric H G)
               (r_coset_rel_transitive H G).
Qed.
