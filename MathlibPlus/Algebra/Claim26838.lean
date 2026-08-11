import Mathlib

namespace MathlibPlus.Algebra.Claim26838

/-- Additivity alone is enough for the alternating Cartesian identity. -/
theorem alternatingCartesianCycle {R S : Type*} [Ring R] [AddCommGroup S]
    (J : R →+ S) (A₀ A₁ C₀ C₁ : R) :
    J (A₀ * C₀) - J (A₀ * C₁) - J (A₁ * C₀) + J (A₁ * C₁) =
      J ((A₁ - A₀) * (C₁ - C₀)) := by
  rw [show (A₁ - A₀) * (C₁ - C₀) =
      A₁ * C₁ - A₁ * C₀ - A₀ * C₁ + A₀ * C₀ by noncomm_ring]
  rw [J.map_add, J.map_sub, J.map_sub]
  abel

end MathlibPlus.Algebra.Claim26838
