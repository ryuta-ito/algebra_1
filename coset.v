Require Export group.
Require Export relation.

Set Implicit Arguments.
Unset Strict Implicit.

Definition left_coset_rel (M : Type) (G : group M) (H : sub_group G) : relation M :=
  fun x => fun y => (bin G (inverse G x) y) \in H.

Definition right_coset_rel (M : Type) (G : group M) (H : sub_group G) : relation M :=
  fun x => fun y => (bin G y (inverse G x)) \in H.

Definition left_coset (M : Type) (G : group M) (H : sub_group G) (x : M) : set M :=
  fun y => left_coset_rel H x y.

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

Definition right_coset (M : Type) (G : group M) (H : sub_group G)(x : M) : set M :=
  fun y => right_coset_rel H x y.

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

Theorem left_coset_eq_left_coset' : forall (M : Type) (G : group M) (H : sub_group G) x,
  same_set (left_coset H x) (left_coset' H G x).
Proof.
  intros.
  split.
  -
    simpl.
    unfold left_coset,left_coset',left_coset_rel.
    intros s inv_x_s_in_H.
    apply belongs__exists in inv_x_s_in_H.
    inversion inv_x_s_in_H as [h HP].
    inversion HP as [h_in_H eq].
    exists h.
    split.
    +
      assumption.
    +
      rewrite <- eq.
      rewrite assoc.
      rewrite invR.
      rewrite idL.
      reflexivity.
  -
    simpl.
    unfold left_coset,left_coset',left_coset_rel.
    intros s HP.
    inversion HP as [h [h_in_H eq]].
    rewrite eq.
    rewrite assoc.
    rewrite invL.
    rewrite idL.
    assumption.
Qed.

Theorem right_coset_eq_right_coset' : forall (M : Type) (G : group M) (H : sub_group G) x,
  same_set (right_coset H x) (right_coset' H G x).
Proof.
  intros.
  split.
  -
    simpl.
    unfold right_coset,right_coset',right_coset_rel.
    intros s s_inv_x_in_H.
    apply belongs__exists in s_inv_x_in_H.
    inversion s_inv_x_in_H as [h HP].
    inversion HP as [h_in_H eq].
    exists h.
    split.
    +
      assumption.
    +
      rewrite <- eq.
      rewrite <- assoc.
      rewrite invL.
      rewrite idR.
      reflexivity.
  -
    simpl.
    unfold right_coset,right_coset',right_coset_rel.
    intros s HP.
    inversion HP as [h [h_in_H eq]].
    rewrite eq.
    rewrite <- assoc.
    rewrite invR.
    rewrite idR.
    assumption.
Qed.

Theorem l_coset_rel_reflexive : forall (M : Type) (G : group M) (H : sub_group G), reflexive (left_coset_rel H).
Proof.
  simpl.
  intros.
  unfold left_coset_rel.
  rewrite (invL G x).
  apply (sub_group_has_id H).
Qed.

Theorem r_coset_rel_reflexive : forall (M : Type) (G : group M) (H : sub_group G), reflexive (right_coset_rel H).
Proof.
  simpl.
  intros.
  unfold right_coset_rel.
  rewrite (invR G x).
  apply (sub_group_has_id H).
Qed.

Theorem l_coset_rel_symmetric : forall (M : Type) (G : group M) (H : sub_group G), symmetric (left_coset_rel H).
Proof.
  simpl.
  unfold left_coset_rel.
  intros M G H x y inv_x_y_in_H.
  apply inv_belongs in inv_x_y_in_H as inv__inv_x_y_in_H.
  rewrite (sub_group_inverse_eq inv_x_y_in_H) in inv__inv_x_y_in_H.
  rewrite inverse_distributive in inv__inv_x_y_in_H.
  rewrite inverse_eq in inv__inv_x_y_in_H.
  assumption.
Qed.

Theorem r_coset_rel_symmetric : forall (M : Type) (G : group M) (H : sub_group G), symmetric (right_coset_rel H).
Proof.
  simpl.
  unfold right_coset_rel.
  intros M G H x y y_inv_x_in_H.
  apply inv_belongs in y_inv_x_in_H as inv__y_inv_x_in_H.
  rewrite (sub_group_inverse_eq y_inv_x_in_H) in inv__y_inv_x_in_H.
  rewrite inverse_distributive in inv__y_inv_x_in_H.
  rewrite inverse_eq in inv__y_inv_x_in_H.
  assumption.
Qed.

Theorem l_coset_rel_transitive : forall (M : Type) (G : group M) (H : sub_group G), transitive (left_coset_rel H).
Proof.
  simpl.
  unfold left_coset_rel.
  intros M G H x y z inv_x_y_in_H inv_y_z_in_H.
  apply (entire inv_x_y_in_H) in inv_y_z_in_H as inv_x_y_inv_y_z_in_H.
  rewrite (sg_bin_eq inv_x_y_in_H inv_y_z_in_H) in inv_x_y_inv_y_z_in_H.
  rewrite <- assoc in inv_x_y_inv_y_z_in_H.
  replace (bin G y (bin G (inverse G y) z))
    with (bin G (bin G y (inverse G y)) z)
    in inv_x_y_inv_y_z_in_H
    by (rewrite assoc; reflexivity).
  rewrite invR in inv_x_y_inv_y_z_in_H.
  rewrite idL in inv_x_y_inv_y_z_in_H.
  assumption.
Qed.

Theorem r_coset_rel_transitive : forall (M : Type) (G : group M) (H : sub_group G), transitive (right_coset_rel H).
Proof.
  simpl.
  unfold right_coset_rel.
  intros M G H x y z y_inv_x_in_H z_inv_y_in_H.
  apply (entire z_inv_y_in_H) in y_inv_x_in_H as z_inv_y_y_inv_x_in_H.
  rewrite (sg_bin_eq z_inv_y_in_H y_inv_x_in_H) in z_inv_y_y_inv_x_in_H.
  rewrite <- assoc in z_inv_y_y_inv_x_in_H.
  replace (bin G (inverse G y) (bin G y (inverse G x)))
    with (bin G (bin G (inverse G y) y) (inverse G x))
    in z_inv_y_y_inv_x_in_H
    by (rewrite assoc; reflexivity).
  rewrite invL in z_inv_y_y_inv_x_in_H.
  rewrite idL in z_inv_y_y_inv_x_in_H.
  assumption.
Qed.

Definition l_coset_eq_R (M : Type) (G : group M) (H : sub_group G) : eq_R M :=
  Build_eq_R (@l_coset_rel_reflexive M G H)
             (@l_coset_rel_symmetric M G H)
             (@l_coset_rel_transitive M G H).

Definition r_coset_eq_R (M : Type) (G : group M) (H : sub_group G) : eq_R M :=
  Build_eq_R (@r_coset_rel_reflexive M G H)
             (@r_coset_rel_symmetric M G H)
             (@r_coset_rel_transitive M G H).

(* alpha : gH |-> Hg^(-1) *)
Inductive alpha (M : Type) (G : group M) (H : sub_group G) : set M -> set M -> Prop :=
| alpha_R : forall g, g \in G ->
                      (alpha H
                             (eq_class (l_coset_eq_R H) g)
                             (eq_class (r_coset_eq_R H) (inverse G g))).

(* well-defined *)
Theorem alpha_is_map_rel : forall (M : Type) (G : group M) (H : sub_group G),
  map_rel (alpha H).
Proof.
  intros M G H.
  simpl.
  intros x y y' Halpha_y Halpha_y'.
  inversion Halpha_y as [g g_in_G Halpha_y_domain Halpha_y_range].
  inversion Halpha_y' as [g0 g0_in_G Halpha_y'_domain Halpha_y'_range].
  assert (Heq:=Halpha_y_domain).
  rewrite <- Halpha_y'_domain in Heq.
  assert (g0_in_g0H := x_belongs_x_eq_class (l_coset_eq_R H) g0).
  rewrite <- Heq in g0_in_g0H.
  rename g0_in_g0H into g0_in_gH.
  simpl in g0_in_gH.
  assert (gH_eq_gH' := left_coset_eq_left_coset' H g).
  inversion gH_eq_gH' as [gH_subseq_gH' _].
  apply gH_subseq_gH' in g0_in_gH as g0_in_gH'.
  simpl in g0_in_gH'.
  unfold left_coset' in g0_in_gH'.
  inversion g0_in_gH' as [h [h_in_H g0_eq_gh]].
  rewrite g0_eq_gh.
  rewrite inverse_distributive.
  assert ((bin G (inverse G h) (inverse G g))\in (eq_class (r_coset_eq_R H) (inverse G g)))
    as inv_h_inv_g_in_H_inv_g.
  -
    apply inv_belongs in h_in_H as inv_h_in_H.
    apply inv_belongs in g_in_G as inv_g_in_G.
    assert (inv_h_inv_g_in_Hg' := (@g_in_G_h_in_H__gh_in_Hg
                                   M H G (inverse H h) (inverse G g)
                                   inv_h_in_H inv_g_in_G)).
    assert (Hg_eq_Hg' := right_coset_eq_right_coset' H (inverse G g)).
    inversion Hg_eq_Hg' as [_ Hg'_subseq_Hg].
    apply Hg'_subseq_Hg in inv_h_inv_g_in_Hg' as inv_h_inv_g_in_Hg.
    unfold right_coset in inv_h_inv_g_in_Hg.
    rewrite (sub_group_inverse_eq h_in_H) in inv_h_inv_g_in_Hg.
    assumption.
  -
    assert (H_inv_g_eq_H_inv_h_inv_g := @belongs_y_in_x_eq_class__x_eq_class_eq_y_eq_class M
                      (inverse G g)
                      (bin G (inverse G h) (inverse G g))
                      (r_coset_eq_R H) inv_h_inv_g_in_H_inv_g).
    rewrite same_set__eq in H_inv_g_eq_H_inv_h_inv_g.
    assumption.
Qed.

(* beta : Hg |-> g^(-1)H *)
Inductive beta (M : Type) (G : group M) (H : sub_group G) : set M -> set M -> Prop :=
| beta_R : forall g, g \in G ->
                     (beta H
                       (eq_class (r_coset_eq_R H) g)
                       (eq_class (l_coset_eq_R H) (inverse G g))).

Theorem alpha_inverse_beta : forall (M : Type) (G : group M) (H : sub_group G),
  inverse_rel (alpha H) (beta H).
Proof.
  simpl.
  intros.
  inversion H0.
  assert (H4 := (@beta_R M G H (inverse G g))).
  rewrite inverse_eq in H4.
  apply (H4 (inv_belongs H1)).
Qed.

(* |gH| = |H| *)
Theorem gH_same_order_H : forall (M : Type) (G : group M) (H : sub_group G) g,
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
