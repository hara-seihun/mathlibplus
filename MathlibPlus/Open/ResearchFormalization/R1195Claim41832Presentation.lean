import Mathlib
import MathlibPlus.Open.ResearchBatchHallControls

namespace MathlibPlus.Open.ResearchFormalization.R1195Claim41832

open MathlibPlus.Open.ResearchBatchHallControls

/-- The three relators in the displayed presentation, on the named
    generators `a` and `b`. -/
def presentationRelators (m : ℕ) : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of (0 : Fin 2)) ^ m,
    (FreeGroup.of (1 : Fin 2)) ^ 8,
    (FreeGroup.of (1 : Fin 2))⁻¹ * FreeGroup.of (0 : Fin 2) *
        FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2)}

/-- Exact presentation means an isomorphism from the presented group to the
    concrete `ZMod m × ZMod 8` carrier, carrying the two generators to the
    displayed elements and transporting multiplication to `gmMul`. -/
def presentedByAandB (m : ℕ) : Prop :=
  ∃ e : PresentedGroup (presentationRelators m) ≃ Gm m,
    e (PresentedGroup.of (0 : Fin 2)) = gmA m ∧
      e (PresentedGroup.of (1 : Fin 2)) = gmB m ∧
        ∀ x y : PresentedGroup (presentationRelators m),
          e (x * y) = gmMul m (e x) (e y)

/-- The concrete `E(C_m,8)` carrier is exactly the semidirect product with
    the displayed presentation, without adding an unsupported restriction on
    the natural parameter `m`. -/
def claim41832 : Prop :=
  ∀ m : ℕ, presentedByAandB m

end MathlibPlus.Open.ResearchFormalization.R1195Claim41832
