Require Export group.
Require Export relation.

Set Implicit Arguments.
Unset Strict Implicit.

Definition left_coset_rel (M : Type) (G : group M) (H : sub_group G) : relation M :=
  fun x => fun y => (bin G (inverse G x) y) \in H.
Arguments left_coset_rel M G H /.

Definition right_coset_rel (M : Type) (G : group M) (H : sub_group G) : relation M :=
  fun x => fun y => (bin G y (inverse G x)) \in H.
Arguments right_coset_rel M G H /.

Definition left_coset (M : Type) (G : group M) (H : sub_group G) (x : M) : set M :=
  fun y => left_coset_rel H x y.
Arguments left_coset M G H x /.

Definition left_coset' (M : Type) (H G : group M) (x : M) : set M :=
  fun y => exists h, h \in H /\ y = bin G x h.
Arguments left_coset' M H G x /.

Lemma g_in_G_h_in_H__gh_in_gH : forall (M : Type) (H G : group M) h g,
  h \in H -> g \in G ->
  (bin G g h) \in (left_coset' H G g) .
Proof.
  intros.
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
Arguments right_coset M G H x /.

Definition right_coset' (M : Type) (H G : group M) (x : M) : set M :=
  fun y => exists h, h \in H /\ y = bin G h x.
Arguments right_coset' M H G x /.

Lemma g_in_G_h_in_H__gh_in_Hg : forall (M : Type) (H G : group M) h g,
  h \in H -> g \in G ->
  (bin G h g) \in (right_coset' H G g).
Proof.
  intros.
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
  rewrite (invL G x).
  apply (sub_group_has_id H).
Qed.

Theorem r_coset_rel_reflexive : forall (M : Type) (G : group M) (H : sub_group G), reflexive (right_coset_rel H).
Proof.
  simpl.
  intros.
  rewrite (invR G x).
  apply (sub_group_has_id H).
Qed.

Theorem l_coset_rel_symmetric : forall (M : Type) (G : group M) (H : sub_group G), symmetric (left_coset_rel H).
Proof.
  simpl.
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

(* N ◁ G -> g ∈ G -> gN = Ng *)
Theorem normal_group_coset_is_same : forall (M : Type) (G : group M) (N : normal_group G) g,
  g \in G -> same_set (left_coset' N G g) (right_coset' N G g).
Proof.
  simpl.
  intros M G N g g_in_G.
  split.
  - (* -> *)
    intros n n_in_gN.
    inversion n_in_gN as [n' [n'_in_N n_eq]].
    assert (bin G (bin G g n') (inverse G g) \in N) as n''_in_N
    by apply (ng_low g_in_G n'_in_N).
    remember (bin G (bin G g n') (inverse G g)) as n''.

    apply (both_sides_R (bin G)) with (z:=g) in Heqn''.
    rewrite <- assoc in Heqn''.
    rewrite invL in Heqn''.
    rewrite idR in Heqn''.

    apply (both_sides_L (bin G)) with (z:=(inverse G g)) in Heqn''.
    rewrite assoc in Heqn''.
    rewrite assoc in Heqn''.
    rewrite invL in Heqn''.
    rewrite idL in Heqn''.

    rewrite <- Heqn'' in n_eq.
    rewrite assoc in n_eq.
    rewrite assoc in n_eq.
    rewrite invR in n_eq.
    rewrite idL in n_eq.

    exists n''.
    split.
    + assumption.
    + assumption.
  - (* <- *)
    intros n n_in_gN.
    inversion n_in_gN as [n' [n'_in_N n_eq]].
    apply inv_belongs in g_in_G as inv_g_in_G.
    apply (ng_low inv_g_in_G) in n'_in_N as inv_g_n'_g_in_N.
    rewrite inverse_eq in inv_g_n'_g_in_N.
    remember (bin G (bin G (inverse G g) n') g) as n''.

    apply (both_sides_R (bin G)) with (z:=(inverse G g)) in Heqn''.
    rewrite <- assoc in Heqn''.
    rewrite invR in Heqn''.
    rewrite idR in Heqn''.

    apply (both_sides_L (bin G)) with (z:=g) in Heqn''.
    rewrite assoc in Heqn''.
    rewrite assoc in Heqn''.
    rewrite invR in Heqn''.
    rewrite idL in Heqn''.

    rewrite <- Heqn'' in n_eq.
    rewrite <- assoc in n_eq.
    rewrite invL in n_eq.
    rewrite idR in n_eq.

    exists n''.
    split.
    + assumption.
    + assumption.
Qed.

(* (gN, hN) |-> ghN *)
Inductive coset_op (M : Type) (G : group M) (N : normal_group G) : set M -> set M -> set M -> Prop :=
| coset_op_R : forall g h,
    g \in G ->
    h \in G ->
    (coset_op N (left_coset' N G g)
                (left_coset' N G h)
                (left_coset' N G (bin G g h))).

Definition set_coset (M : Type) (S T : set M) (bin : M -> M -> M) : set M :=
  fun x => exists s t, x = bin s t /\ s \in S /\ t \in T.
Arguments set_coset M S T bin /.

(* (gN)(hN) = ghN *)
Theorem coset_op_is_hom : forall (M : Type) (G : group M) (N : normal_group G) g h,
  g \in G -> h \in G ->
  same_set
    (set_coset (left_coset' N G g) (left_coset' N G h) (bin G))
    (left_coset' N G (bin G g h)).
Proof.
  simpl.
  intros M G N g h g_in_G h_in_G.
  split.
  - (* -> *)
    intros gn'hn''.
    intros gn'hn''_in_gNhN.
    inversion gn'hn''_in_gNhN as [gn' [hn'' [gn'hn''_eq [[n' [n'_in_N n'_eq]] [n'' [n''_in_N n''_eq]]]]]].
    rewrite n'_eq in gn'hn''_eq.
    rewrite n''_eq in gn'hn''_eq.
    assert (n' = bin G (bin G h (inverse G h)) n') as n'_eq'
      by (rewrite invR; rewrite idL; reflexivity).
    rewrite n'_eq' in gn'hn''_eq.
    rewrite <- assoc in gn'hn''_eq.
    rewrite <- assoc in gn'hn''_eq.
    rewrite <- assoc in gn'hn''_eq.
    replace (bin G g _)
      with (bin G (bin G g h) (bin G (inverse G h) (bin G n' (bin G h n''))))
      in gn'hn''_eq
      by (rewrite <- assoc; reflexivity).

    replace(bin G (inverse G h) (bin G n' (bin G h n'')))
      with (bin G (bin G (inverse G h) n') (bin G h n''))
      in gn'hn''_eq
      by (rewrite <- assoc; reflexivity).

    replace (bin G (bin G (inverse G h) n') (bin G h n''))
      with (bin G (bin G (bin G (inverse G h) n') h) n'')
      in gn'hn''_eq
      by (rewrite <- assoc; reflexivity).

    assert (inv_h_n'_h := ng_low (inv_belongs h_in_G) n'_in_N).
    rewrite inverse_eq in inv_h_n'_h.

    exists (bin G (bin G (bin G (inverse G h) n') h) n'').
    split.
    +
      assert (eq := entire inv_h_n'_h n''_in_N).
      rewrite sg_bin_eq in eq by (assumption; assumption).
      assumption.
    +
      assumption.
  - (* <- *)
    intros s ghn.
    inversion ghn as [n [n_in_N s_eq]].
    assert (g = bin G g (id G)) as eq
      by (rewrite idR; reflexivity).
    rewrite eq in s_eq.
    rewrite <- assoc in s_eq.
    rewrite <- assoc in s_eq.

    replace (bin G g (bin G (id G) (bin G h n)))
      with (bin G (bin G g (id G)) (bin G h n))
      in s_eq
      by (rewrite <- assoc; reflexivity).

    exists (bin G g (id G)).
    exists (bin G h n).

    split.
    +
      assumption.
    +
      split.
      *
        exists (id G).
        split.
        --
           apply sub_group_has_id.
        --
           reflexivity.
      *
        exists n.
        split.
        --
           assumption.
        --
           reflexivity.
Qed.

Theorem coset_op_eq : forall (M : Type) (G : group M) (N : normal_group G) g h,
  g \in G -> h \in G ->
    (set_coset (left_coset' N G g) (left_coset' N G h) (bin G)) =
    (left_coset' N G (bin G g h)).
Proof.
  intros.
  rewrite <- same_set__eq.
  apply coset_op_is_hom.
  assumption.
  assumption.
Qed.

Theorem coset_op_is_map_rel : forall (M : Type) (G : group M) (N : normal_group G),
  bin_map_rel (coset_op N).
Proof.
  simpl.
  intros M G N x y z z' coset_op_1 coset_op_2.
  inversion coset_op_1 as [g h g_in_G h_in_G x_eq y_eq].
  inversion coset_op_2 as [g' h' g'_in_G h'_in_G  x_eq' y_eq'].
  rewrite <- (coset_op_eq N g_in_G h_in_G).
  rewrite <- (coset_op_eq N g'_in_G h'_in_G).
  rewrite x_eq.
  rewrite y_eq.
  rewrite x_eq'.
  rewrite y_eq'.
  reflexivity.
Qed.
