Require Export set.

Set Implicit Arguments.
Unset Strict Implicit.

Structure group M := {
  cset :> set M;
  id : M;
  id_belongs : id \in cset;
  bin : M -> M -> M;
  inverse : M -> M;
  inv_belongs : forall g, g \in cset -> (inverse g) \in cset;
  entire : forall x y, x \in cset -> y \in cset -> (bin x y) \in cset;
  assoc : forall x y z, bin x (bin y z) = bin (bin x y) z;
  idR : forall g, bin g id = g;
  idL : forall g, bin id g = g;
  invR : forall g, bin g (inverse g) = id;
  invL : forall g, bin (inverse g) g = id
}.

Structure sub_group M G := {
  sg_group :> group M;
  sg_bin_eq : forall g g', g \in sg_group -> g' \in sg_group -> bin sg_group g g' = bin G g g';
  sg_subset : sg_group \subset G;
}.

Structure normal_group M (G : group M) := {
  ng_sub_group :> sub_group G;
  ng_low : forall h g,
    g \in G -> h \in ng_sub_group ->
    (bin G (bin G g h) (inverse G g)) \in ng_sub_group
}.

Definition set_of_group (M : Type) (G : group M) := fun x => cset G x.
Coercion set_of_group : group >-> Funclass.

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
  (forall g, g \in H -> g \in G) /\
  forall g g', g \in H -> g' \in H -> bin H g g' = bin G g g'.
Arguments subgroup M H G /.

Definition normalgroup (M : Type) (H G : group M) :=
  subgroup H G ->
  forall h g,
    g \in G ->
    h \in H ->
    (bin G (bin G g h) (inverse G g)) \in H.
Arguments normalgroup M H G /.

Theorem sub_group_id_eq : forall (M : Type) (G : group M) (H : sub_group G),
  id H = id G.
Proof.
  intros M G H.
  assert (bin G (id H) (id H) = id H) as eq.
  -
    rewrite <- (sg_bin_eq (id_belongs H) (id_belongs H)).
    rewrite idL.
    reflexivity.
  -
    apply (both_sides_L (bin G)) with (z := inverse G (id H)) in eq.
    rewrite invL in eq.
    rewrite assoc in eq.
    rewrite invL in eq.
    rewrite idL in eq.
    assumption.
Qed.

Theorem sub_group_has_id : forall (M : Type) (G : group M) (H : sub_group G),
  (id G) \in H.
Proof.
  intros.
  rewrite <- (sub_group_id_eq H).
  apply (id_belongs H).
Qed.

Theorem sub_group_inverse_eq : forall (M : Type) (G : group M) (H : sub_group G) x,
  x \in H -> inverse H x = inverse G x.
Proof.
  intros M G H x x_in_H.
  assert (bin G x (inverse H x) = bin H x (inverse H x)) as eq
  by (symmetry; apply (sg_bin_eq x_in_H (inv_belongs x_in_H))).
  rewrite invR in eq.
  rewrite sub_group_id_eq in eq.
  apply (both_sides_L (bin G) (inverse G x)) in eq.
  rewrite idR in eq.
  rewrite assoc in eq.
  rewrite invL in eq.
  rewrite idL in eq.
  assumption.
Qed.

Inductive group_gen (M : Type) (S : set M) (G : group M) : M -> Prop :=
| group_gen_id : group_gen S G (id G)
| group_gen_base : forall g,
    S \subset G -> g \in S -> group_gen S G g
| group_gen_base_inverse : forall g,
    S \subset G -> g \in S -> group_gen S G (inverse G g)
| group_gen_bin : forall g g',
    group_gen S G g -> group_gen S G g' -> group_gen S G (bin G g g').

Theorem group_gen_set_has_id : forall (M : Type) (S : set M) (G : group M), (id G) \in (group_gen S G).
Proof.
  simpl. intros.
  apply group_gen_id.
Qed.

Theorem group_gen_set_is_entire : forall (M : Type) (S : set M) (G : group M) g g',
  g \in (group_gen S G) ->
  g' \in (group_gen S G) ->
  (bin G g g') \in (group_gen S G).
Proof.
  intros. apply (group_gen_bin H H0).
Qed.

Theorem group_gen_set_has_inverse : forall (M : Type) (S : set M) (G : group M) g,
  g \in (group_gen S G) ->
  (inverse G g) \in (group_gen S G).
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

Theorem gen_group_is_minimum : forall (M : Type) (S : set M) (G : group M) (H : sub_group G),
  S \subset G -> S \subset H -> (gen_group S G) \subset H.
Proof.
  simpl.
  intros M S G H S_subset_G S_subset_H s s_in_S'.
  induction s_in_S'.
  - (* s is id *)
    apply (sub_group_has_id H).
  - (* s ∈ S *)
    apply (S_subset_H g H1).
  - (* s ∈ S *)
    rewrite <- (sub_group_inverse_eq (S_subset_H g H1)).
    apply (inv_belongs (S_subset_H g H1)).
  - (* s = s's'',  s',s'' ∈ <S> *)
    rewrite <- (sg_bin_eq IHs_in_S'1 IHs_in_S'2).
    apply (entire IHs_in_S'1 IHs_in_S'2).
Qed.

(* <{ xyx^-1 | x ∈ G, y ∈ S }> *)
Definition minimum_normal_group (M : Type) (S : set M) (G : group M) :=
  let T := (fun g => exists x:M, exists y:M, x \in G /\ y \in S /\ g = bin G (bin G x y) (inverse G x))
  in gen_group T G.

(* T = { xyx^-1 | x ∈ G, y ∈ S }, <T> ◁ G *)
Theorem minimum_normal_group_is_normal_group : forall (M : Type) (S : set M) (G : group M),
  S \subset G -> normalgroup (minimum_normal_group S G) G.
Proof.
  simpl.
  intros M S G H_subset_G H_subgroup_G h g g_in_G h_in_T.
  induction h_in_T as [| h T_subset_G h_in_T | h T_subset_G h_in_T | h h'].
  -
    rewrite idR.
    rewrite invR.
    apply group_gen_id.
  -
    simpl in h_in_T.
    inversion h_in_T as [x h_in_T0].
    inversion h_in_T0 as [y h_in_T1].
    inversion h_in_T1 as [x_in_G [y_in_S h_eq_x_y_inv_x]].
    rewrite h_eq_x_y_inv_x.
    apply group_gen_base.
    + assumption.
    +
      simpl.
      exists (bin G g x).
      exists y.
      split.
      * apply (entire g_in_G x_in_G).
      *
        split.
        -- assumption.
        --
           rewrite <- assoc.
           rewrite <- assoc.
           rewrite <- inverse_distributive.
           rewrite assoc.
           rewrite assoc.
           reflexivity.
  -
    simpl in h_in_T.
    inversion h_in_T as [x h_in_T0].
    inversion h_in_T0 as [y h_in_T1].
    inversion h_in_T1 as [x_in_G [y_in_S h_eq_x_y_inv_x]].
    rewrite h_eq_x_y_inv_x.
    replace ((bin G (bin G g (inverse G (bin G (bin G x y) (inverse G x)))) (inverse G g)))
    with (inverse G (inverse G ((bin G (bin G g (inverse G (bin G (bin G x y) (inverse G x)))) (inverse G g)))))
    by (rewrite inverse_eq; reflexivity).
    apply group_gen_base_inverse.
    + assumption.
    +
      simpl.
      exists (bin G g x).
      exists y.
      split.
      *
        apply (entire g_in_G x_in_G).
      *
        split.
        --
           assumption.
        --
           rewrite inverse_distributive.
           rewrite inverse_eq.
           rewrite inverse_distributive.
           rewrite inverse_eq.
           rewrite inverse_distributive.
           rewrite <- assoc.
           rewrite <- assoc.
           rewrite assoc.
           rewrite assoc.
           reflexivity.
  -
    replace h with (bin G h (bin G (inverse G g) g))
    by (rewrite invL; rewrite idR; reflexivity).
    +
      assert (IHhh'_in_T := group_gen_bin IHh_in_T1 IHh_in_T2).
      rewrite <- assoc in IHhh'_in_T.
      rewrite <- assoc in IHhh'_in_T.
      rewrite <- assoc in IHhh'_in_T.
      rewrite <- assoc.
      rewrite <- assoc.
      rewrite <- assoc.
      rewrite <- assoc.
      assumption.
Qed.

(* S ⊆ <{xyx^-1 | x ∈ G, y ∈ S}> *)
Theorem minimum_normal_group_lemma : forall (M : Type) (G : group M) (S : set M),
  S \subset G -> S \subset (minimum_normal_group S G).
Proof.
  simpl.
  intros M G S S_subset_G s s_in_S.
  apply group_gen_base.
  -
    simpl.
    intros s' P.
    inversion P as [x P'].
    inversion P' as [y P''].
    inversion P'' as [x_in_G [y_in_S s'_eq]].
    rewrite s'_eq.
    apply S_subset_G in y_in_S as y_in_G.
    apply inv_belongs in x_in_G as inv_x_in_G.
    apply (entire (entire x_in_G y_in_G) inv_x_in_G).
  -
    simpl.
    exists (id G).
    exists s.
    split.
    +
      apply id_belongs.
    +
      split.
      *
        assumption.
      *
        rewrite idL.
        rewrite id_inverse_eq_id.
        rewrite idR.
        reflexivity.
Qed.

(* S ⊆ N -> N ◁ G -> <{xyx^-1 | x ∈ G, y ∈ S}> ⊆ N *)
Theorem minimum_normal_group_lemma0 : forall (M : Type) (S : set M) (G : group M) (N : normal_group G),
  subset S N -> subset (minimum_normal_group S G) N.
Proof.
  simpl.
  intros M S G N S_subset_N n n_in_N'.
  induction n_in_N' as [|n _ n_in_N'|n _ n_in_N'| n n'].
  -
    rewrite <- (sub_group_id_eq N).
    apply id_belongs.
  -
    simpl in n_in_N'.
    inversion n_in_N' as [x [y [x_in_G [y_in_S n_eq]]]].
    rewrite n_eq.
    apply (ng_low x_in_G (S_subset_N y y_in_S)).
  -
    simpl in n_in_N'.
    inversion n_in_N' as [x [y [x_in_G [y_in_S n_eq]]]].
    rewrite n_eq.
    rewrite inverse_distributive.
    rewrite inverse_eq.
    rewrite inverse_distributive.
    rewrite assoc.
    rewrite <- (sub_group_inverse_eq (S_subset_N y y_in_S)).
    apply (ng_low x_in_G (inv_belongs (S_subset_N y y_in_S))).
  -
    rewrite <- (sg_bin_eq IHn_in_N'1 IHn_in_N'2).
    apply (entire IHn_in_N'1 IHn_in_N'2).
Qed.

(* H, S, T ⊆ G, H = <T>, G = <S>        *)
(* (∀x ∈ S ∀y ∈ T, x*y*x^-1 ∈ T) -> H ◁ G *)
Theorem normal_group_mitigative_condition : forall (M : Type) (G : group M) (S T : set M),
  T \subset S -> S \subset G ->
  (forall x y,
    x \in S -> y \in T ->
    (bin G (bin G x y) (inverse G x)) \in (group_gen T G)/\
    (bin G (bin G (inverse G x) y) x) \in (group_gen T G)) ->
    normalgroup (gen_group T G) (gen_group S G).
Proof.
  simpl.
  intros M G S T
         T_subset_S S_subset_G
         mitigative_normal_group_assumption
         T'_subgroup_S' h g
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
