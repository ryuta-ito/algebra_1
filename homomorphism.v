Require Import group.

Set Implicit Arguments.
Unset Strict Implicit.

Structure hom M (G : group M) M' (G' : group M') := {
  hom_f : M -> M';
  hom_is_map : map hom_f G G';
  hom_law : forall x y, hom_f (bin G x y) = bin G' (hom_f x) (hom_f y)
}.

Theorem hom_id_map_id : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  hom_f h (id G) = id G'.
Proof.
  intros.
  assert (hom_f h (id G) = hom_f h (bin G (id G) (id G)))
    as f_id_G_eq_f__id_G_id_G
    by (rewrite (idR G (id G)); reflexivity).

  rewrite (hom_law h (id G) (id G)) in f_id_G_eq_f__id_G_id_G.
  rename f_id_G_eq_f__id_G_id_G into f_id_G_eq_f_id_G_f_id_G.

  apply (both_sides_L (bin G') (inverse G' (hom_f h (id G)))) in f_id_G_eq_f_id_G_f_id_G.
  rename f_id_G_eq_f_id_G_f_id_G into inv_f_id_G_f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.

  rewrite (assoc G' (inverse G' (hom_f h (id G))) (hom_f h (id G)) (hom_f h (id G)))
    in inv_f_id_G_f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.

  rewrite (invL G' (hom_f h (id G)))
    in inv_f_id_G_f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.
  rename inv_f_id_G_f_id_G_eq_inv_f_id_G_f_id_G_f_id_G
    into f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.

  rewrite (idL G' (hom_f h (id G))) in f_id_G_eq_inv_f_id_G_f_id_G_f_id_G.
  symmetry.
  assumption.
Qed.

Theorem hom_inverse_map_inverse : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  forall x, hom_f h (inverse G x) = inverse G' (hom_f h x).
Proof.
  intros.
  assert (f_id_G_eq_id_G' := hom_id_map_id h).

  rewrite <- (invR G x) in f_id_G_eq_id_G'.
  rename f_id_G_eq_id_G' into f_x_x'_eq_id_G'.
  rewrite (hom_law h x (inverse G x)) in f_x_x'_eq_id_G'.
  rename f_x_x'_eq_id_G' into f_x_f_x'_eq_id_G'.

  apply (both_sides_L (bin G'))
    with (z:=(inverse G' (hom_f h x)))
    in f_x_f_x'_eq_id_G'
    as f_x'_f_x_f_x'_eq_f_x'_id_G'.
  rewrite (assoc G' (inverse G' (hom_f h x)) (hom_f h x) (hom_f h (inverse G x))) in f_x'_f_x_f_x'_eq_f_x'_id_G'.

  rewrite (idR G' (inverse G' (hom_f h x)))
    in f_x'_f_x_f_x'_eq_f_x'_id_G'.
  rename f_x'_f_x_f_x'_eq_f_x'_id_G' into f_x'_f_x_f_x'_eq_f_x'.

  rewrite (invL G' (hom_f h x)) in f_x'_f_x_f_x'_eq_f_x'.
  rename f_x'_f_x_f_x'_eq_f_x' into id_G'_f_x'_eq_f_x'.

  rewrite (idL G' (hom_f h (inverse G x))) in id_G'_f_x'_eq_f_x'.
  rename id_G'_f_x'_eq_f_x' into f_x'_eq_f_x'.
  assumption.
Qed.

Definition kernel (M M' : Type) (G : group M) (G' : group M') (h : hom G G') : set M :=
  fun x => hom_f h x = id G'.
Arguments kernel M M' G G' h /.

Theorem kernel_has_id : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  belongs (id G) (kernel h).
Proof.
  simpl. intros.
  apply hom_id_map_id.
Qed.

Theorem kernel_is_entire : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  forall x y, belongs x (kernel h) -> belongs y (kernel h) -> belongs (bin G x y) (kernel h).
Proof.
  simpl. intros.
  assert (f_xy_eq_fx_fy := hom_law h x y).
  rewrite H in f_xy_eq_fx_fy.
  rewrite H0 in f_xy_eq_fx_fy.
  rename f_xy_eq_fx_fy into f_xy_eq_id_G'_id_G'.

  rewrite (idR G' (id G')) in f_xy_eq_id_G'_id_G'.
  assumption.
Qed.

Theorem kernel_has_inverse : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  forall x, belongs x (kernel  h) -> belongs (inverse G x) (kernel h).
Proof.
  simpl. intros.
  rewrite (hom_inverse_map_inverse h x).
  rewrite H.
  rewrite id_inverse_eq_id.
  reflexivity.
Qed.

Definition image (M M' : Type) (G : group M) (G' : group M') (h : hom G G') : set M' :=
  fun x => exists y, hom_f h y = x.
Arguments image M M' G G' h /.

Theorem image_has_id : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  belongs (id G') (image h).
Proof.
  simpl. intros.
  exists (id G).
  apply hom_id_map_id.
Qed.

Theorem image_is_entire : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  forall x y, belongs x (image h) -> belongs y (image h) -> belongs (bin G' x y) (image h).
Proof.
  simpl.
  intros.
  inversion H as [x1].
  inversion H0 as [y1].
  exists (bin G x1 y1).
  rewrite <- H1.
  rewrite <- H2.
  rewrite (hom_law h).
  reflexivity.
Qed.

Theorem image_has_inverse : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  forall x, belongs x (image h) -> belongs (inverse G' x) (image h).
Proof.
  simpl. intros.
  inversion H.
  exists (inverse G x0).
  rewrite <- H0.
  apply hom_inverse_map_inverse.
Qed.


(* 準同型f: G -> G' に対し、 fが単射である <-> Ker(f) = {id_G} *)

Theorem hom_is_injection_iff_kernel_is_id : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  injection (hom_f h) G G' <->
  forall x y, belongs x (kernel h) -> belongs y (kernel h) -> x = y /\ x = id G.
Proof.
  simpl. intros.
  split.
  - (* -> *)
    intros.
    split.
    +
      rewrite <- H1 in H0.
      apply (H (hom_is_map h) x y H0).
    +
      assert (H2 := hom_id_map_id h).
      rewrite <- H2 in H0.
      apply (H (hom_is_map h) x (id G) H0).
  - (* <- *)
    intros.
    assert (H2 := hom_law h x (inverse G y)).
    rewrite (hom_inverse_map_inverse h y) in H2.
    rewrite H1 in H2.
    rewrite (invR G') in H2.
    assert (H3 := H (bin G x (inverse G y)) (id G) H2 (hom_id_map_id h)).
    inversion H3.
    apply (both_sides_R (bin G)) with (z := y) in H4.
    rewrite <- (assoc G) with (z := y) in H4.
    rewrite (invL G y) in H4.
    rewrite (idR G x) in H4.
    rewrite (idL G y) in H4.
    assumption.
Qed.

Section g_Aut_G_hom.
  Variables M : Type.
  Variables G : group M.
  Definition M' := M -> M.
  Variables G' : group M'.

  Definition i g := fun h:M => bin G (bin G g h) (inverse G g).
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

  Axiom extensionality : forall (X Y:Type) (x:X) (f g:X->Y),
    f x = g x -> f = g.
  Theorem f_sat_hom_law : forall g1 g2, f (bin G g1 g2) = (comp (f g1) (f g2)).
  Proof.
    simpl.
    intros.
    apply (@extensionality M M g1).
    rewrite (inverse_distributive G g1 g2).
    rewrite <- (assoc G g1 g2 g1).
    rewrite (assoc G (bin G g1 (bin G g2 g1)) (inverse G g2) (inverse G g1)).
    rewrite <- (assoc G g1 (bin G g2 g1) (inverse G g2)).
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
    id_f (bin G x y) = bin G (id_f x) (id_f y).
  Proof.
    simpl. intros.
    unfold id_f.
    reflexivity.
  Qed.

  Theorem id_is_hom : hom G G.
  Proof.
    apply (Build_hom id_is_map id_sat_hom_law).
  Qed.
End id_is_hom.

Definition kernel_group (M M' : Type) (G : group M) (G' : group M') (h : hom G G') : group M :=
  Build_group
   (kernel_has_id h)
   (@kernel_has_inverse M M' G G' h)
   (@kernel_is_entire M M' G G' h)
   (assoc G)
   (idR G) (idL G)
   (invR G) (invL G).

Theorem kernel_group_is_normal_group : forall (M M' : Type) (G : group M) (G' : group M') (h : hom G G'),
  normal_group (kernel_group h) G.
Proof.
  simpl. intros.
  rewrite hom_law. rewrite hom_law.
  rewrite H1.
  rewrite idR.
  rewrite hom_inverse_map_inverse.
  rewrite invR.
  reflexivity.
Qed.
