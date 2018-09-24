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
