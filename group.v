Require Export set.

Set Implicit Arguments.
Unset Strict Implicit.

Structure group M := {
  cset :> set M;
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

Lemma both_sides_L : forall (M : Type) (bin : M -> M -> M) (x y z : M),
  x = y -> bin z x = bin z y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma both_sides_R : forall (M : Type) (bin : M -> M -> M) (x y z : M),
  x = y -> bin x z = bin y z.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma id_inverse_eq_id : forall (M : Type) (G : group M),
  inverse G (id G) = id G.
Proof.
  intros.
  assert (H := idR G (id G)).
  apply (both_sides_L (bin G))
    with (z := (inverse G (id G))) in H.
  rewrite (invL G (id G)) in H.
  rewrite (assoc G (inverse G (id G)) (id G) (id G)) in H.
  rewrite (idR G (inverse G (id G))) in H.
  rewrite (idR G (inverse G (id G))) in H.
  assumption.
Qed.

Lemma inverse_eq : forall (M : Type) (G : group M) g,
  inverse G (inverse G g) = g.
Proof.
  intros.
  assert (bin G (inverse G g) (inverse G (inverse G g)) = id G)
    by (rewrite invR; reflexivity).
  apply (both_sides_L (bin G)) with (z := g) in H.
  rewrite assoc in H.
  rewrite invR in H.
  rewrite idL in H.
  rewrite idR in H.
  assumption.
Qed.

Lemma inverse_distributive : forall (M : Type) (G : group M) g g',
  inverse G (bin G g g') = bin G (inverse G g') (inverse G g).
Proof.
  intros.
  assert (bin G g' (inverse G g') = id G) by (apply (invR G g')).
  apply (both_sides_L (bin G)) with (z := g) in H.
  apply (both_sides_R (bin G)) with (z := (inverse G g)) in H.
  rewrite (idR G g) in H.
  rewrite (invR G g) in H.
  rewrite <- (assoc G g (bin G g' (inverse G g')) (inverse G g)) in H.
  rewrite <- (assoc G g' (inverse G g') (inverse G g)) in H.
  rewrite (assoc G g g' (bin G (inverse G g') (inverse G g))) in H.
  apply (both_sides_L (bin G)) with (z := inverse G (bin G g g')) in H.
  rewrite (idR G (inverse G (bin G g g'))) in H.
  rewrite (assoc G (inverse G (bin G g g')) (bin G g g') (bin G (inverse G g') (inverse G g))) in H.
  rewrite (invL G (bin G g g')) in H.
  rewrite (idL G (bin G (inverse G g') (inverse G g))) in H.
  symmetry.
  assumption.
Qed.

Definition subgroup (M : Type) (H G : group M) :=
  (forall g, belongs g H -> belongs g G) /\
  forall g g', belongs g H -> belongs g' H -> bin H g g' = bin G g g'.
Arguments subgroup M H G /.

Definition normal_group (M : Type) (H G : group M) := forall h g,
  subgroup H G ->
  belongs g G ->
  belongs h H ->
  belongs (bin G (bin G g h) (inverse G g)) H.
Arguments normal_group M H G /.

Theorem subgroup_id_eq : forall (M : Type) (H G : group M),
  subgroup H G -> id H = id G.
Proof.
  simpl. intros.
  inversion H0.
  assert (bin G (id H) (id H) = id H).
  -
    rewrite <- (H2 (id H) (id H) (id_belongs H) (id_belongs H)).
    apply (idL H (id H)).
  -
    apply (both_sides_L (bin G)) with (z := inverse G (id H)) in H3.
    rewrite (invL G (id H)) in H3.
    rewrite (assoc G (inverse G (id H)) (id H) (id H)) in H3.
    rewrite (invL G (id H)) in H3.
    rewrite (idL G (id H)) in H3.
    assumption.
Qed.

Theorem subgroup_has_id : forall (M : Type) (H G : group M),
  subgroup H G -> belongs (id G) H.
Proof.
  intros.
  rewrite <- (subgroup_id_eq H0).
  apply (id_belongs H).
Qed.

Theorem subgroup_inverse_eq : forall (M : Type) (H G : group M) x,
  subgroup H G ->
  belongs x H ->
  inverse H x = inverse G x.
Proof.
  intros.
  inversion H0.
  assert (bin H x (inverse H x) = bin G x (inverse H x))
    by (apply (H3 x (inverse H x) H1 (inv_belongs H1))).
  rewrite (invR H x) in H4.
  rewrite (subgroup_id_eq H0) in H4.
  apply (both_sides_L (bin G)) with (z := inverse G x) in H4.
  rewrite (idR G (inverse G x)) in H4.
  rewrite (assoc G) in H4.
  rewrite (invL G x) in H4.
  rewrite (idL G) in H4.
  symmetry.
  assumption.
Qed.

Inductive group_gen (M : Type) (S : set M) (G : group M) : M -> Prop :=
| group_gen_id : group_gen S G (id G)
| group_gen_base : forall g,
    subset S G -> belongs g S -> group_gen S G g
| group_gen_base_inverse : forall g,
    subset S G -> belongs g S -> group_gen S G (inverse G g)
| group_gen_bin : forall g g',
    group_gen S G g -> group_gen S G g' -> group_gen S G (bin G g g').

Theorem group_gen_set_has_id : forall (M : Type) (S : set M) (G : group M), belongs (id G) (group_gen S G).
Proof.
  simpl. intros.
  apply group_gen_id.
Qed.

Theorem group_gen_set_is_entire : forall (M : Type) (S : set M) (G : group M) g g',
  belongs g (group_gen S G) ->
  belongs g' (group_gen S G) ->
  belongs (bin G g g') (group_gen S G).
Proof.
  intros. apply (group_gen_bin H H0).
Qed.

Theorem group_gen_set_has_inverse : forall (M : Type) (S : set M) (G : group M) g,
  belongs g (group_gen S G) ->
  belongs (inverse G g) (group_gen S G).
Proof.
  simpl.
  intros.
  induction H.
  -
    rewrite id_inverse_eq_id.
    apply group_gen_id.
  -
    apply (group_gen_base_inverse H H0).
  -
    rewrite inverse_eq.
    apply (group_gen_base H H0).
  -
    rewrite inverse_distributive.
    apply (group_gen_bin IHgroup_gen2 IHgroup_gen1).
Qed.

Definition gen_group (M : Type) (S :set M) (G : group M) :=
  Build_group
    (group_gen_set_has_id S G)
    (@group_gen_set_has_inverse M S G)
    (@group_gen_set_is_entire M S G)
    (assoc G)
    (idR G) (idL G)
    (invR G) (invL G).

(* H, S, T ⊆ G, H = <T>, G = <S>        *)
(* (∀x ∈ S ∀y ∈ T, x*y*x^-1 ∈ T) -> H ◁ G *)
Theorem normal_group_mitigative_condition : forall (M : Type) (G : group M) (S T : set M),
  subset T S -> subset S G ->
  (forall x y,
    belongs x S -> belongs y T ->
    belongs (bin G (bin G x y) (inverse G x))
            (group_gen T G) /\
    belongs (bin G (bin G (inverse G x) y) x)
            (group_gen T G)) ->
    normal_group (gen_group T G) (gen_group S G).
Proof.
  simpl.
  intros M G S T
         T_subset_S S_subset_G
         mitigative_normal_group_assumption
         h g T'_subgroup_S'
         g_in_S'.
  generalize h.  (* important!! *)
  induction g_in_S'
  as [| g _ g_in_S
      | g _ g_in_S
      | g' g'' g'_in_S' IH_g'_in_S' g''_in_S' IH_g''_in_S'].
  - (* group_gen_id of g *)
    intros h' h'_in_T'.
    rewrite id_inverse_eq_id.
    rewrite idL.
    rewrite idR.
    assumption.
  - (* group_gen_base of g *)
    intros h' h'_in_T'.
    induction h'_in_T'
    as [| h' _ h'_in_T
        | h' _ h'_in_T
        | h' h'' h'_in_T' IH_h'_in_T' h''_in_T' IH_h''_in_T'].
    + (* group_gen_id of h *)
      rewrite idR.
      rewrite invR.
      apply group_gen_id.
    + (* group_gen_base of h *)
      apply (mitigative_normal_group_assumption g h' g_in_S h'_in_T).
    + (* group_gen_base_inverse of h *)
      assert (tmp := mitigative_normal_group_assumption g h' g_in_S h'_in_T).
      inversion tmp as [g_h'_inv_g_in_T' _]. clear tmp.
      apply group_gen_set_has_inverse in g_h'_inv_g_in_T' as inv__g_h'_inv_g_in_T'.
      simpl in inv__g_h'_inv_g_in_T'.
      rewrite inverse_distributive in inv__g_h'_inv_g_in_T'.
      rewrite inverse_eq in inv__g_h'_inv_g_in_T'.
      rewrite inverse_distributive in inv__g_h'_inv_g_in_T'.
      rewrite <- assoc.
      assumption.
    + (* group_gen_bin of h *)
      replace h' with (bin G h' (bin G (inverse G g) g)).
      *
        replace (bin G h' (bin G (inverse G g) g))
        with (bin G (bin G h' (inverse G g)) g)
        by (symmetry; apply assoc).

        replace (bin G (bin G (bin G h' (inverse G g)) g) h'')
        with (bin G (bin G h' (inverse G g)) (bin G g h''))
        by apply assoc.

        replace (bin G g (bin G (bin G h' (inverse G g)) (bin G g h'')))
        with (bin G (bin G g (bin G h' (inverse G g))) (bin G g h''))
        by (symmetry; apply assoc).

        replace (bin G (bin G (bin G g (bin G h' (inverse G g))) (bin G g h'')) (inverse G g))
        with (bin G (bin G g (bin G h' (inverse G g))) (bin G (bin G g h'') (inverse G g)))
        by apply assoc.

        rewrite <- assoc in IH_h'_in_T'.
        apply (group_gen_bin IH_h'_in_T' IH_h''_in_T').
      *
        rewrite invL.
        rewrite idR.
        reflexivity.
  - (* group_gen_base_inverse of g *)
    intros h' h'_in_T'.
    induction h'_in_T'
    as [| h' _ h'_in_T
        | h' _ h'_in_T
        | h' h'' h'_in_T' IH_h'_in_T' h''_in_T' IH_h''_in_T'].
    + (* group_gen_id of h *)
      rewrite idR.
      rewrite invR.
      apply group_gen_id.
    + (* group_gen_base of h *)
      rewrite inverse_eq.
      apply (mitigative_normal_group_assumption g h' g_in_S h'_in_T).
    + (* group_gen_base_inverse of h *)
      rewrite inverse_eq.
      assert (tmp := mitigative_normal_group_assumption g h' g_in_S h'_in_T).
      inversion tmp as [_ inv_g_h'_g_in_T']. clear tmp.
      apply group_gen_set_has_inverse in inv_g_h'_g_in_T' as inv__inv_g_h'_g_in_T'.
      simpl in inv__inv_g_h'_g_in_T'.
      rewrite inverse_distributive in inv__inv_g_h'_g_in_T'.
      rewrite inverse_distributive in inv__inv_g_h'_g_in_T'.
      rewrite inverse_eq in inv__inv_g_h'_g_in_T'.
      rewrite <- assoc.
      assumption.
    + (* group_gen_bin of h *)
      rewrite inverse_eq.
      replace h' with (bin G h' (bin G g (inverse G g))).
      *
        replace (bin G h' (bin G g (inverse G g)))
        with (bin G (bin G h' g) (inverse G g))
        by (symmetry; apply assoc).

        replace (bin G (bin G (bin G h' g) (inverse G g)) h'')
        with (bin G (bin G h' g) (bin G (inverse G g) h''))
        by apply assoc.

        replace (bin G (inverse G g) (bin G (bin G h' g) (bin G (inverse G g) h'')))
        with (bin G (bin G (inverse G g) (bin G h' g)) (bin G (inverse G g) h''))
        by (symmetry; apply assoc).

        replace (bin G (bin G (bin G (inverse G g) (bin G h' g)) (bin G (inverse G g) h'')) g)
        with (bin G (bin G (inverse G g) (bin G h' g)) (bin G (bin G (inverse G g) h'') g))
        by apply assoc.

        rewrite <- assoc in IH_h'_in_T'.
        rewrite inverse_eq in IH_h'_in_T'.
        rewrite inverse_eq in IH_h''_in_T'.
        apply (group_gen_bin IH_h'_in_T' IH_h''_in_T').
      *
        rewrite invR.
        rewrite idR.
        reflexivity.
  - (* group_gen_bin of g *)
    intros h' h'_in_T'.
    rewrite inverse_distributive.
    replace (bin G (bin G g' g'') h')
    with (bin G g' (bin G g'' h'))
    by apply assoc.

    replace (bin G (bin G g' (bin G g'' h'))
                     (bin G (inverse G g'') (inverse G g')))
    with (bin G (bin G (bin G g' (bin G g'' h')) (inverse G g''))
                  (inverse G g'))
    by (symmetry; apply assoc).

    replace (bin G (bin G g' (bin G g'' h')) (inverse G g''))
    with (bin G g' (bin G (bin G g'' h') (inverse G g'')))
    by apply assoc.

    assert (g''_h'_inv_g''_in_T := IH_g''_in_S' h' h'_in_T').
    apply (IH_g'_in_S' (bin G (bin G g'' h') (inverse G g'')) g''_h'_inv_g''_in_T).
Qed.
