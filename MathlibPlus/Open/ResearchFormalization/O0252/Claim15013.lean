import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0252

/-- Claim 15013: the exact two-wave splitting of the Dini factor, whose
independent carrier is the quotient displayed in Claim 15010. -/
noncomputable def claim15013_exactTwoWaveSplitting : Prop :=
  ∀ (L : ℝ) (z : ℂ),
    z ≠ Complex.I / 2 →
    z ≠ -Complex.I / 2 →
    let G : ℂ :=
      (z * Complex.sin ((L : ℂ) * z) -
          (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
        (z ^ 2 + (1 / 4 : ℂ))
    G =
      (Complex.I / 2) *
          Complex.exp (-Complex.I * (L : ℂ) * z) /
            (z - Complex.I / 2) -
        (Complex.I / 2) *
          Complex.exp (Complex.I * (L : ℂ) * z) /
            (z + Complex.I / 2)

end MathlibPlus.Open.ResearchFormalization.O0252
