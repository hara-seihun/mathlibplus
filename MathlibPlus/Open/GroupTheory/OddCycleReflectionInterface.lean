import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace MathlibPlus.Open.GroupTheory

/-- Claim 53191: two odd regular cycles with reversing involutions admit a
simultaneous conjugator.  Transitivity of the cyclic action is the
p-point-cycle condition on `Fin p`. -/
def oddCycleReflectionInterface : Prop :=
  ∀ (p : ℕ), Odd p →
    ∀ (c d ι κ : Equiv.Perm (Fin p)),
      (∀ x y : Fin p, ∃ k : ℕ, (c ^ k) x = y) →
      (∀ x y : Fin p, ∃ k : ℕ, (d ^ k) x = y) →
      ι * ι = 1 →
      κ * κ = 1 →
      ι * c * ι = c⁻¹ →
      κ * d * κ = d⁻¹ →
      ∃ h : Equiv.Perm (Fin p),
        h * c * h⁻¹ = d ∧ h * ι * h⁻¹ = κ

end MathlibPlus.Open.GroupTheory
