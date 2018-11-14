Require Import group.

Structure hom M (G : group M) M' (G' : group M') := {
  hom_f : M -> M';
  hom_is_map : map hom_f G G';
  hom_law : forall x y, hom_f (bin M G x y) = bin M' G' (hom_f x) (hom_f y)
}.

Theorem hom_id_map_id : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  hom_f M G M' G' h (id M G) = id M' G'.
Proof.
  intros.
  assert (hom_f M G M' G' h (id M G) = hom_f M G M' G' h (bin M G (id M G) (id M G)))
    as f_id_G_eq_f__id_G_id_G
    by (rewrite (idR M G (id M G)); reflexivity).

  rewrite (hom_law M G M' G' h (id M G) (id M G)) in f_id_G_eq_f__id_G_id_G.
  rename f_id_G_eq_f__id_G_id_G into f_id_G_eq_f_id_G_f_id_G.

  apply (both_sides_L (bin M' G') (hom_f M G M' G' h (id M G)) (bin M' G' (hom_f M G M' G' h (id M G)) (hom_f M G M' G' h (id M G))) (inverse M' G' (hom_f M G M' G' h (id M G))))
    in f_id_G_eq_f_id_G_f_id_G.
  rename f_id_G_eq_f_id_G_f_id_G into inv_f_id_G_f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.

  rewrite (assoc M' G' (inverse M' G' (hom_f M G M' G' h (id M G))) (hom_f M G M' G' h (id M G)) (hom_f M G M' G' h (id M G)))
    in inv_f_id_G_f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.

  rewrite (invL M' G' (hom_f M G M' G' h (id M G)))
    in inv_f_id_G_f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.
  rename inv_f_id_G_f_id_G_eq_inv_f_id_G_f_id_G_f_id_G
    into f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.

  rewrite (idL M' G' (hom_f M G M' G' h (id M G))) in f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.
  symmetry.
  assumption.
Qed.

Theorem hom_inverse_map_inverse : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  forall x, hom_f M G M' G' h (inverse M G x) = inverse M' G' (hom_f M G M' G' h x).
Proof.
  intros.
  assert (f_id_G_eq_id_G' := hom_id_map_id G G' h).

  rewrite <- (invR M G x) in f_id_G_eq_id_G'.
  rename f_id_G_eq_id_G' into f_x_x'_eq_id_G'.
  rewrite (hom_law M G M' G' h x (inverse M G x)) in f_x_x'_eq_id_G'.
  rename f_x_x'_eq_id_G' into f_x_f_x'_eq_id_G'.

  apply (both_sides_L (bin M' G'))
    with (z:=(inverse M' G' (hom_f M G M' G' h x)))
    in f_x_f_x'_eq_id_G'
    as f_x'_f_x_f_x'_eq_f_x'_id_G'.
  rewrite (assoc M' G' (inverse M' G' (hom_f M G M' G' h x)) (hom_f M G M' G' h x) (hom_f M G M' G' h (inverse M G x))) in f_x'_f_x_f_x'_eq_f_x'_id_G'.

  rewrite (idR M' G' (inverse M' G' (hom_f M G M' G' h x)))
    in f_x'_f_x_f_x'_eq_f_x'_id_G'.
  rename f_x'_f_x_f_x'_eq_f_x'_id_G' into f_x'_f_x_f_x'_eq_f_x'.

  rewrite (invL M' G' (hom_f M G M' G' h x)) in f_x'_f_x_f_x'_eq_f_x'.
  rename f_x'_f_x_f_x'_eq_f_x' into id_G'_f_x'_eq_f_x'.

  rewrite (idL M' G' (hom_f M G M' G' h (inverse M G x))) in id_G'_f_x'_eq_f_x'.
  rename id_G'_f_x'_eq_f_x' into f_x'_eq_f_x'.
  assumption.
Qed.

Definition kernel {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G') : set M :=
  fun x => hom_f M G M' G' h x = id M' G'.
Arguments kernel {M M'} G G' h /.

Theorem kernel_has_id : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  belongs (id M G) (kernel G G' h).
Proof.
  simpl. intros.
  apply hom_id_map_id.
Qed.

Theorem kernel_is_entire : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  forall x y, belongs x (kernel G G' h) -> belongs y (kernel G G' h) -> belongs (bin M G x y) (kernel G G' h).
Proof.
  simpl. intros.
  assert (f_xy_eq_fx_fy := hom_law M G M' G' h x y).
  rewrite H in f_xy_eq_fx_fy.
  rewrite H0 in f_xy_eq_fx_fy.
  rename f_xy_eq_fx_fy into f_xy_eq_id_G'_id_G'.

  rewrite (idR M' G' (id M' G')) in f_xy_eq_id_G'_id_G'.
  assumption.
Qed.

Theorem kernel_has_inverse : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  forall x, belongs x (kernel G G' h) -> belongs (inverse M G x) (kernel G G' h).
Proof.
  simpl. intros.
  rewrite (hom_inverse_map_inverse G G' h x).
  rewrite H.
  rewrite id_inverse_eq_id.
  reflexivity.
Qed.

Definition image {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G') : set M' :=
  fun x => exists y, hom_f M G M' G' h y = x.
Arguments image {M M'} G G' h /.

Theorem image_has_id : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  belongs (id M' G') (image G G' h).
Proof.
  simpl. intros.
  exists (id M G).
  apply hom_id_map_id.
Qed.

Theorem image_is_entire : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  forall x y, belongs x (image G G' h) -> belongs y (image G G' h) -> belongs (bin M' G' x y) (image G G' h).
Proof.
  simpl.
  intros.
  inversion H as [x1].
  inversion H0 as [y1].
  exists (bin M G x1 y1).
  rewrite <- H1.
  rewrite <- H2.
  rewrite (hom_law M G M' G' h).
  reflexivity.
Qed.

Theorem image_has_inverse : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  forall x, belongs x (image G G' h) -> belongs (inverse M' G' x) (image G G' h).
Proof.
  simpl. intros.
  inversion H.
  exists (inverse M G x0).
  rewrite <- H0.
  apply hom_inverse_map_inverse.
Qed.


(* 準同型f: G -> G' に対し、 fが単射である <-> Ker(f) = {id_G} *)

Theorem hom_is_injection_iff_kernel_is_id : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  injection (hom_f M G M' G' h) G G' <->
  forall x y, belongs x (kernel G G' h) -> belongs y (kernel G G' h) -> x = y /\ x = id M G.
Proof.
  simpl. intros.
  split.
  - (* -> *)
    intros.
    split.
    +
      rewrite <- H1 in H0.
      apply (H (hom_is_map M G M' G' h) x y H0).
    +
      assert (H2 := hom_id_map_id G G' h).
      rewrite <- H2 in H0.
      apply (H (hom_is_map M G M' G' h) x (id M G) H0).
  - (* <- *)
    intros.
    assert (H2 := hom_law M G M' G' h x (inverse M G y)).
    rewrite (hom_inverse_map_inverse G G' h y) in H2.
    rewrite H1 in H2.
    rewrite (invR M' G') in H2.
    assert (H3 := H (bin M G x (inverse M G y)) (id M G) H2 (hom_id_map_id G G' h)).
    inversion H3.
    apply (both_sides_R (bin M G)) with (z := y) in H4.
    rewrite <- (assoc M G) with (z := y) in H4.
    rewrite (invL M G y) in H4.
    rewrite (idR M G x) in H4.
    rewrite (idL M G y) in H4.
    assumption.
Qed.

Section g_Aut_G_hom.
  Variables M : Type.
  Variables G : group M.
  Definition M' := M -> M.
  Variables G' : group M'.

  Definition i g := fun h:M => bin M G (bin M G g h) (inverse M G g).
  (* i_g h = g h g^(-1) *)
  Arguments i g /.
  Definition f g := i g.  (* f: G -> Aut G
                             f: g |-> i g *)
  Arguments f g /.

  Definition comp (f f' : M') :=
    fun x => f (f' x).
  Arguments comp f f' /.

  Theorem f_is_map : map f G G'.
  Proof.
  Admitted.

  Axiom extensionality : forall {X Y:Type} (x:X) (f g:X->Y),
    f x = g x -> f = g.
  Theorem f_sat_hom_law : forall g1 g2, f (bin M G g1 g2) = (comp (f g1) (f g2)).
  Proof.
    simpl.
    intros.
    apply (extensionality g1).
    rewrite (inverse_distributive G g1 g2).
    rewrite <- (assoc M G g1 g2 g1).
    rewrite (assoc M G (bin M G g1 (bin M G g2 g1)) (inverse M G g2) (inverse M G g1)).
    rewrite <- (assoc M G g1 (bin M G g2 g1) (inverse M G g2)).
    reflexivity.
  Qed.
End g_Aut_G_hom.

Section id_is_hom.
  Variables M : Type.
  Variables G : group M.

  Definition id_f := fun x:M => x.

  Theorem id_is_map : map id_f G G.
  Proof.
    simpl. intros.
    unfold id_f.
    assumption.
  Qed.

  Theorem id_sat_hom_law : forall x y,
    id_f (bin M G x y) = bin M G (id_f x) (id_f y).
  Proof.
    simpl. intros.
    unfold id_f.
    reflexivity.
  Qed.

  Theorem id_is_hom : hom M G M G.
  Proof.
    apply (Build_hom M G M G id_f id_is_map id_sat_hom_law).
  Qed.
End id_is_hom.

Definition kernel_group {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G') : group M :=
  Build_group M
   (kernel G G' h)
   (id M G)
   (kernel_has_id G G' h)
   (bin M G)
   (inverse M G)
   (kernel_has_inverse G G' h)
   (kernel_is_entire G G' h)
   (assoc M G)
   (idR M G) (idL M G)
   (invR M G) (invL M G).

Theorem kernel_group_is_normal_group : forall {M M' : Type} (G : group M) (G' : group M') (h : hom M G M' G'),
  normal_group (kernel_group G G' h) G.
Proof.
  simpl. intros.
  rewrite hom_law. rewrite hom_law.
  rewrite H1.
  rewrite idR.
  rewrite hom_inverse_map_inverse.
  rewrite invR.
  reflexivity.
Qed.
