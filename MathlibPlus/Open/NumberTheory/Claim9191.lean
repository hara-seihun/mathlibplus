import MathlibPlus.Open.NumberTheory.Claim9192

namespace MathlibPlus.Open.NumberTheory.Claim9191

open MathlibPlus.Open.NumberTheory.Claim9192

noncomputable section

/-- The algebraic-unit carrier used for a real Mahler-fixed number. -/
def realAlgebraicUnit (β : ℝ) : Prop :=
  IsIntegral ℤ β ∧ IsIntegral ℤ β⁻¹

/-- A real algebraic unit fixed by Mahler measure is Pisot or Salem. -/
def mahlerFixedUnitIsPisotOrSalem : Prop :=
  ∀ β : ℝ,
    1 < β →
    realAlgebraicUnit β →
    mahlerMeasure (β : ℂ) = β →
    (∀ z ∈ conjugateRoots (β : ℂ), z ≠ (β : ℂ) → ‖z‖ ≤ 1) ∧
      (PisotNumber β ∨ SalemNumber β)

end

end MathlibPlus.Open.NumberTheory.Claim9191
