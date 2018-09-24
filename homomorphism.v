Require Import group.

Theorem hom_id_map_id : forall {M_1 M_2 : Type} (G_1 : set M_1) bin_1 (G_2 : set M_2) bin_2 (f : M_1 -> M_2),
  group G_1 bin_1 ->
  group G_2 bin_2 ->
  map f G_1 G_2 ->
    homomorphism G_1 bin_1 G_2 bin_2 f ->
    forall id_G_1 id_G_2,
      id G_1 id_G_1 bin_1 ->
      id G_2 id_G_2 bin_2 ->
      f id_G_1 = id_G_2.
Proof.
  intros M_1 M_2 G_1 bin_1 G_2 bin_2 f G_1_is_group G_2_is_group f_is_map f_is_hom.
  intros id_G_1 id_G_2 id_G_1_is_id id_G_2_is_id.
  apply id_belongs in id_G_1_is_id as id_G_1_belongs_G_1.
  unfold id in id_G_1_is_id.
  apply id_G_1_is_id in id_G_1_belongs_G_1 as id_G_1_eq_.
  inversion id_G_1_eq_ as [id_G_1_eq _]. clear id_G_1_eq_.
  (* id_G_1_eq : bin_1 id_G_1 id_G_1 = id_G_1 *)

  assert (f id_G_1 = f (bin_1 id_G_1 id_G_1)) as f_id_G_1_eq_f_id_G_1_id_G_1 by (rewrite id_G_1_eq; reflexivity).
  (* f_id_G_1_eq_f_id_G_1_id_G_1 : f id_G_1 = f (bin_1 id_G_1 id_G_1) *)

  unfold homomorphism in f_is_hom.
  apply (f_is_hom G_1_is_group G_2_is_group f_is_map id_G_1 id_G_1 id_G_1_belongs_G_1) in id_G_1_belongs_G_1 as f_id_G_1_eq.
  rewrite f_id_G_1_eq in f_id_G_1_eq_f_id_G_1_id_G_1.
  rename f_id_G_1_eq_f_id_G_1_id_G_1 into f_id_G_1_eq_f_id_G_1_f_id_G_1.
  (* f_id_G_1_eq_f_id_G_1_f_id_G_1 : f id_G_1 = bin_2 (f id_G_1) (f id_G_1) *)

  apply (group_has_g_inverse_g' G_2 bin_2 (f id_G_1) (f_is_map id_G_1 id_G_1_belongs_G_1)) in G_2_is_group as f_id_G_1_inv_.
  inversion f_id_G_1_inv_ as [f_id_G_1' [f_id_G_1'_belongs_G_2 f_id_G_1_inv___]].
  (* f_id_G_1' : M_2 *)

  assert (bin_2 f_id_G_1' (f id_G_1) = bin_2 f_id_G_1' (bin_2 (f id_G_1) (f id_G_1)))
  as f_id_G_1'_id_G_1_eq_f_id_G_1'_f_id_G_1_f_id_G_1.
  -
    replace (bin_2 f_id_G_1' (f id_G_1))
    with (bin_2 f_id_G_1' (bin_2 (f id_G_1) (f id_G_1))).
    +
      reflexivity.
    +
      rewrite <- f_id_G_1_eq_f_id_G_1_f_id_G_1.
      reflexivity.
  -
    apply f_is_map in id_G_1_belongs_G_1 as f_id_G_1_belongs_G_2.
    apply group_has_assoc in G_2_is_group as G_2_assoc.
    unfold associative in G_2_assoc.
    rewrite (G_2_assoc f_id_G_1' (f id_G_1) (f id_G_1) f_id_G_1'_belongs_G_2 f_id_G_1_belongs_G_2 f_id_G_1_belongs_G_2) in f_id_G_1'_id_G_1_eq_f_id_G_1'_f_id_G_1_f_id_G_1.
    (* f_id_G_1'_id_G_1_eq_f_id_G_1'_f_id_G_1_f_id_G_1 :                          *)
    (* bin_2 f_id_G_1' (f id_G_1) = bin_2 (bin_2 f_id_G_1' (f id_G_1)) (f id_G_1) *)

    apply f_id_G_1_inv___ in f_id_G_1'_belongs_G_2 as f_id_G_1_inv____.
    inversion f_id_G_1_inv____ as [_ f_id_G_1'_f_id_G_1_eq_f_id_G_1__].
    unfold id in  f_id_G_1'_f_id_G_1_eq_f_id_G_1__.
    specialize f_id_G_1'_f_id_G_1_eq_f_id_G_1__ with (f id_G_1).
    apply f_id_G_1'_f_id_G_1_eq_f_id_G_1__
    in f_id_G_1_belongs_G_2
    as f_id_G_1'_f_id_G_1_eq_f_id_G_1_.
    inversion f_id_G_1'_f_id_G_1_eq_f_id_G_1_ as [_ f_id_G_1'_f_id_G_1_eq_f_id_G_1].
    rewrite f_id_G_1'_f_id_G_1_eq_f_id_G_1 in f_id_G_1'_id_G_1_eq_f_id_G_1'_f_id_G_1_f_id_G_1.
    (* f_id_G_1'_id_G_1_eq_f_id_G_1'_f_id_G_1_f_id_G_1 :  *)
    (* bin_2 f_id_G_1' (f id_G_1) = f id_G_1             *)

    apply (specific_inverse_to_id G_2 bin_2 (f id_G_1) f_id_G_1' id_G_2 G_2_is_group id_G_2_is_id) in f_id_G_1_inv___ as f_id_G_1'_f_id_G_1_eq_id_G_2_.
    inversion f_id_G_1'_f_id_G_1_eq_id_G_2_ as [_ f_id_G_1'_f_id_G_1_eq_id_G_2].
    rewrite f_id_G_1'_f_id_G_1_eq_id_G_2 in f_id_G_1'_id_G_1_eq_f_id_G_1'_f_id_G_1_f_id_G_1.
    symmetry.
    assumption.
Qed.

Theorem hom_inverse_map_inverse : forall {M_1 M_2 : Type} (G_1 : set M_1) bin_1 (G_2 : set M_2) bin_2 (f : M_1 -> M_2),
  group G_1 bin_1 ->
  group G_2 bin_2 ->
  map f G_1 G_2 ->
    homomorphism G_1 bin_1 G_2 bin_2 f ->
    forall g g' f_g',
      belongs g G_1  ->
      belongs g' G_1  ->
      belongs f_g' G_2  ->
      inverse G_1 g g' bin_1 ->
      inverse G_2 (f g) f_g' bin_2 ->
      f g' = f_g'.
Proof.
  intros M_1 M_2 G_1 bin_1 G_2 bin_2 f G_1_is_group G_2_is_group f_is_map.
  intros f_is_hom g g' f_g' g_belongs_G_1 g'_belongs_G_1 f_g'_belongs_G_2 g_inverse_g' f_g_inverse_f_g'.
  apply (group_has_id G_1 bin_1) in G_1_is_group as G_1_id_.
  apply (group_has_id G_2 bin_2) in G_2_is_group as G_2_id_.
  inversion G_1_id_ as [id_G_1 [id_G_1_belongs G_1_is_id]].
  inversion G_2_id_ as [id_G_2 [id_G_2_belongs G_2_is_id]].
  apply (hom_id_map_id G_1 bin_1 G_2 bin_2 f G_1_is_group G_2_is_group f_is_map f_is_hom id_G_1 id_G_2 G_1_is_id) in G_2_is_id as f_id_G_1_eq_id_G_2.
  (* f_id_G_1_eq_id_G_2 : f id_G_1 = id_G_2 *)

  apply (specific_inverse_to_id G_1 bin_1 g g' id_G_1 G_1_is_group G_1_is_id) in g_inverse_g' as g_g'_is_id_G_1_.
  inversion g_g'_is_id_G_1_ as [g_g'_is_id_G_1 _].
  (* g_g'_is_id_G_1 : bin_1 g g' = id_G_1 *)

  rewrite <- g_g'_is_id_G_1 in f_id_G_1_eq_id_G_2.
  rename f_id_G_1_eq_id_G_2 into f_g_g'_eq_id_G_2.
  (* f_g_g'_eq_id_G_2 : f (bin_1 g g') = id_G_2 *)

  rewrite (f_is_hom G_1_is_group G_2_is_group f_is_map g g' g_belongs_G_1 g'_belongs_G_1) in f_g_g'_eq_id_G_2.
  (* f_g_g'_eq_id_G_2 : bin_2 (f g) (f g') = id_G_2 *)

  assert (bin_2 f_g' (bin_2 (f g) (f g')) = bin_2 f_g' id_G_2)
  as f_g'_f_g_g'_eq_f_g'_id_G_2
  by (rewrite f_g_g'_eq_id_G_2; reflexivity).
  (* f_g'_f_g_g'_eq_f_g'_id_G_2 : bin_2 f_g' (bin_2 (f g) (f g')) = *)
  (*                              bin_2 f_g' id_G_2                 *)

  apply (G_2_is_id f_g') in f_g'_belongs_G_2 as f_g'_id_G_2_eq_f_g'_.
  inversion f_g'_id_G_2_eq_f_g'_ as [f_g'_id_G_2_eq_f_g' _].
  rewrite f_g'_id_G_2_eq_f_g' in f_g'_f_g_g'_eq_f_g'_id_G_2.
  rename f_g'_f_g_g'_eq_f_g'_id_G_2 into f_g'_f_g_g'_eq_f_g'.
  (* f_g'_f_g_g'_eq_f_g' : bin_2 f_g' (bin_2 (f g) (f g')) = f_g' *)

  apply (group_has_assoc G_2 bin_2) in G_2_is_group as G_2_assoc.
  apply (f_is_map g) in g_belongs_G_1 as f_g_belongs_G_2.
  apply (f_is_map g') in g'_belongs_G_1 as f__g'_belongs_G_2.
  rewrite (G_2_assoc f_g' (f g) (f g') f_g'_belongs_G_2 f_g_belongs_G_2 f__g'_belongs_G_2) in f_g'_f_g_g'_eq_f_g'.
  (* f_g'_f_g_g'_eq_f_g' : bin_2 (bin_2 f_g' (f g)) (f g') = f_g' *)

  apply (specific_inverse_to_id G_2 bin_2 (f g) f_g' id_G_2 G_2_is_group G_2_is_id) in f_g_inverse_f_g' as f_g'_f_g_eq_id_G_2_.
  inversion f_g'_f_g_eq_id_G_2_ as [_ f_g'_f_g_eq_id_G_2].
  rewrite f_g'_f_g_eq_id_G_2 in f_g'_f_g_g'_eq_f_g'.
  rename f_g'_f_g_g'_eq_f_g' into id_G_2__f_g'_eq_f_g'.
  (* f_g'_id_G_2_eq_f_g' : bin_2 f_g' id_G_2 = f_g' *)

  apply (G_2_is_id (f g')) in f__g'_belongs_G_2 as id_G_2_f_g'_eq_f_g'_.
  inversion id_G_2_f_g'_eq_f_g'_ as [_ id_G_2_f_g'_eq_f_g'].
  rewrite id_G_2_f_g'_eq_f_g' in id_G_2__f_g'_eq_f_g'.
  rename id_G_2__f_g'_eq_f_g' into f__g'_eq_f_g'.
  assumption.
Qed.
