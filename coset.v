Require Export group.
Require Export relation.

Definition left_coset_rel {M : Type} (H G : group M) : relation M :=
  fun x => fun y =>
    subgroup H G -> belongs (bin M G (inverse M G x) y) (cset M H).

Definition left_coset {M : Type} (H G : group M) (x : M) : set M :=
  fun y => left_coset_rel H G x y.

Definition left_coset' {M : Type} (H G : group M) (x : M) : set M :=
  fun y => exists h, belongs h (cset M H) /\ y = bin M G x h.

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

Theorem left_coset_rel_is_eq_relation : forall {M : Type} (H G : group M), eq_relation (left_coset_rel H G).
Proof.
  simpl. intros.
  unfold left_coset_rel.
  split.
  - (* reflexive *)
    intros.
    rewrite (invL M G x).
    apply (subgroup_has_id H G H0).
  -
    split.
    + (* symmetric *)
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
    + (* transitive *)
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
