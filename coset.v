Require Export group.
Require Export relation.

Set Implicit Arguments.
Unset Strict Implicit.

Definition left_coset_rel (M : Type) (H G : group M) : relation M :=
  fun x => fun y =>
    subgroup H G -> (bin G (inverse G x) y) \in H.

Definition right_coset_rel (M : Type) (H G : group M) : relation M :=
  fun x => fun y =>
    subgroup H G -> (bin G y (inverse G x)) \in H.

Definition left_coset (M : Type) (H G : group M) (x : M) : set M :=
  fun y => left_coset_rel H G x y.

Definition left_coset' (M : Type) (H G : group M) (x : M) : set M :=
  fun y => exists h, h \in H /\ y = bin G x h.

Lemma g_in_G_h_in_H__gh_in_gH : forall (M : Type) (H G : group M) h g,
  h \in H -> g \in G ->
  (bin G g h) \in (left_coset' H G g) .
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

Definition right_coset (M : Type) (H G : group M) (x : M) : set M :=
  fun y => right_coset_rel H G x y.

Definition right_coset' (M : Type) (H G : group M) (x : M) : set M :=
  fun y => exists h, h \in H /\ y = bin G h x.

Lemma g_in_G_h_in_H__gh_in_Hg : forall (M : Type) (H G : group M) h g,
  h \in H -> g \in G ->
  (bin G h g) \in (right_coset' H G g).
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

Theorem left_coset_eq_left_coset' : forall (M : Type) (H G : group M) x,
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

Theorem right_coset_eq_right_coset' : forall (M : Type) (H G : group M) x,
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

Theorem l_coset_rel_reflexive : forall (M : Type) (H G : group M), reflexive (left_coset_rel H G).
Proof.
  simpl.
  intros.
  unfold left_coset_rel.
  intros.
  rewrite (invL G x).
  apply (subgroup_has_id H0).
Qed.

Theorem r_coset_rel_reflexive : forall (M : Type) (H G : group M), reflexive (right_coset_rel H G).
Proof.
  simpl.
  intros.
  unfold right_coset_rel.
  intros.
  rewrite (invR G x).
  apply (subgroup_has_id H0).
Qed.

Theorem l_coset_rel_symmetric : forall (M : Type) (H G : group M), symmetric (left_coset_rel H G).
Proof.
  simpl.
  unfold left_coset_rel.
  intros.
  apply H0 in H1 as H2.
  apply inv_belongs in H2.
  apply inv_belongs in H2 as H3.
  rewrite inverse_eq in H3.
  rewrite (subgroup_inverse_eq H1 H3) in H2.
  rewrite (inverse_distributive G (inverse G x) y) in H2.
  rewrite inverse_eq in H2.
  assumption.
Qed.

Theorem r_coset_rel_symmetric : forall (M : Type) (H G : group M), symmetric (right_coset_rel H G).
Proof.
  simpl.
  unfold right_coset_rel.
  intros.
  apply H0 in H1 as H2.
  apply inv_belongs in H2.
  apply inv_belongs in H2 as H3.
  rewrite inverse_eq in H3.
  rewrite (subgroup_inverse_eq H1 H3) in H2.
  rewrite (inverse_distributive G y (inverse G x)) in H2.
  rewrite inverse_eq in H2.
  assumption.
Qed.

Theorem l_coset_rel_transitive : forall (M : Type) (H G : group M), transitive (left_coset_rel H G).
Proof.
  simpl.
  unfold left_coset_rel.
  intros.
  apply H0 in H2 as H3.
  apply H1 in H2 as H4.
  inversion H2.
  apply (entire H3) in  H4 as H7.
  rewrite (H6 (bin G (inverse G x) y) (bin G (inverse G y) z) H3 H4) in H7.
  rewrite <- assoc in H7.
  replace (bin G y (bin G (inverse G y) z))
    with (bin G (bin G y (inverse G y)) z)
    in H7
    by (rewrite assoc; reflexivity).
  rewrite invR in H7.
  rewrite idL in H7.
  assumption.
Qed.

Theorem r_coset_rel_transitive : forall (M : Type) (H G : group M), transitive (right_coset_rel H G).
Proof.
  simpl.
  unfold right_coset_rel.
  intros.
  apply H0 in H2 as H3.
  apply H1 in H2 as H4.
  inversion H2.
  apply (entire H4) in H3 as H7.
  rewrite (H6 (bin G z (inverse G y)) (bin G y (inverse G x)) H4 H3) in H7.
  rewrite <- assoc in H7.
  replace (bin G (inverse G y) (bin G y (inverse G x)))
    with (bin G (bin G (inverse G y) y) (inverse G x))
    in H7
    by (rewrite assoc; reflexivity).
  rewrite invL in H7.
  rewrite idL in H7.
  assumption.
Qed.

Definition l_coset_eq_R (M : Type) (H G : group M) : eq_R M :=
  Build_eq_R (@l_coset_rel_reflexive M H G)
             (@l_coset_rel_symmetric M H G)
             (@l_coset_rel_transitive M H G).

Definition r_coset_eq_R (M : Type) (H G : group M) : eq_R M :=
  Build_eq_R (@r_coset_rel_reflexive M H G)
             (@r_coset_rel_symmetric M H G)
             (@r_coset_rel_transitive M H G).

(* alpha : gH |-> Hg^(-1) *)
Inductive alpha (M : Type) (H G : group M) : set M -> set M -> Prop :=
| alpha_R : forall g, g \in G ->
                      (alpha H G
                             (eq_class (l_coset_eq_R H G) g)
                             (eq_class (r_coset_eq_R H G) (inverse G g))).

(* well-defined *)
Theorem alpha_is_map_rel : forall (M : Type) (H G : group M),
  subgroup H G -> map_rel (alpha H G).
Proof.
  intros M H G Hsubgroup .
  simpl.
  intros x y y' Halpha_y Halpha_y'.
  inversion Halpha_y as [g g_in_G Halpha_y_domain Halpha_y_range].
  inversion Halpha_y' as [g0 g0_in_G Halpha_y'_domain Halpha_y'_range].
  assert (Heq:=Halpha_y_domain).
  rewrite <- Halpha_y'_domain in Heq.
  assert (g0_in_g0H := x_belongs_x_eq_class (l_coset_eq_R H G) g0).
  rewrite <- Heq in g0_in_g0H.
  rename g0_in_g0H into g0_in_gH.
  simpl in g0_in_gH.
  assert (gH_eq_gH' := left_coset_eq_left_coset' g Hsubgroup).
  inversion gH_eq_gH' as [gH_subseq_gH' _].
  apply gH_subseq_gH' in g0_in_gH as g0_in_gH'.
  simpl in g0_in_gH'.
  unfold left_coset' in g0_in_gH'.
  inversion g0_in_gH' as [h [h_in_H g0_eq_gh]].
  rewrite g0_eq_gh.
  rewrite inverse_distributive.
  assert ((bin G (inverse G h) (inverse G g))\in (eq_class (r_coset_eq_R H G) (inverse G g)))
    as inv_h_inv_g_in_H_inv_g.
  -
    apply inv_belongs in h_in_H as inv_h_in_H.
    apply inv_belongs in g_in_G as inv_g_in_G.
    assert (inv_h_inv_g_in_Hg' := (@g_in_G_h_in_H__gh_in_Hg
                                   M H G (inverse H h) (inverse G g)
                                   inv_h_in_H inv_g_in_G)).
    assert (Hg_eq_Hg' := right_coset_eq_right_coset' (inverse G g) Hsubgroup).
    inversion Hg_eq_Hg' as [_ Hg'_subseq_Hg].
    apply Hg'_subseq_Hg in inv_h_inv_g_in_Hg' as inv_h_inv_g_in_Hg.
    unfold right_coset in inv_h_inv_g_in_Hg.
    rewrite (subgroup_inverse_eq Hsubgroup h_in_H) in inv_h_inv_g_in_Hg.
    assumption.
  -
    assert (H_inv_g_eq_H_inv_h_inv_g := @belongs_y_in_x_eq_class__x_eq_class_eq_y_eq_class M
                      (inverse G g)
                      (bin G (inverse G h) (inverse G g))
                      (r_coset_eq_R H G) inv_h_inv_g_in_H_inv_g).
    rewrite same_set__eq in H_inv_g_eq_H_inv_h_inv_g.
    assumption.
Qed.

(* beta : Hg |-> g^(-1)H *)
Inductive beta (M : Type) (H G : group M) : set M -> set M -> Prop :=
| beta_R : forall g, g \in G ->
                     (beta H G
                       (eq_class (r_coset_eq_R H G) g)
                       (eq_class (l_coset_eq_R H G) (inverse G g))).

Theorem alpha_inverse_beta : forall (M : Type) (H G : group M),
  inverse_rel (alpha H G) (beta H G).
Proof.
  simpl.
  intros.
  inversion H0.
  assert (H4 := (@beta_R M H G (inverse G g))).
  rewrite inverse_eq in H4.
  apply (H4 (inv_belongs H1)).
Qed.

(* |gH| = |H| *)
Theorem gH_same_order_H : forall (M : Type) (H G : group M) g,
  same_order (left_coset' H G g) H.
Proof.
  intros.
  simpl.
  exists (fun h:M => bin G (inverse G g) h).
  split.
  - (* injective *)
    intros.
    apply (both_sides_L (bin G)) with (z := g) in H1.
    rewrite assoc in H1.
    rewrite assoc in H1.
    rewrite invR in H1.
    rewrite idL in H1.
    rewrite idL in H1.
    assumption.
  - (* surjective *)
    intros.
    exists (bin G g y).
    intros.
    rewrite assoc.
    rewrite invL.
    rewrite idL.
    reflexivity.
Qed.
