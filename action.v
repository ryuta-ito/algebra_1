Require Import group.
Require Import Basics.

Open Scope program_scope.

Structure action {M : Type} (G : group M) (X : Type) := {
  phi :> M -> X -> X;
  phi_low1 : forall x, phi (id G) x = x;
  phi_low2 : forall g h x, phi g (phi h x) = phi (bin G g h) x;
}.

Example action_has_inverse {M : Type} (G : group M) (X : Type) (φ : action G X) : forall g, g \in G -> exists φ',
  (forall x, ((φ g) ∘ (φ' g)) x = x) /\ (forall x, ((φ' g) ∘ (φ g)) x = x).
Proof.
  intros.
  exists (fun g => fun x => (φ (inverse G g)) x).
  unfold compose.
  split.
  - (* left *)
    intros.
    rewrite phi_low2.
    rewrite invR.
    rewrite phi_low1.
    reflexivity.
  - (* right *)
    intros.
    rewrite phi_low2.
    rewrite invL.
    rewrite phi_low1.
    reflexivity.
Qed.
