import Mathlib

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.R0344.Claim20175

noncomputable section

noncomputable def beta20175 (U : ℝ) : ℝ :=
  (1 + 7 / 50) / 2 + (901 / 10000 / 4) * Real.log U

noncomputable def residualQ20175 (q : ℕ → ℝ) (U : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 (32768 * 175000000),
    (q n : ℂ) * Real.rpow (n : ℝ) (-beta20175 U) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((U : ℂ) * Real.log (n : ℝ)))

noncomputable def firstOpenBlock20175 : Set ℝ :=
  Set.Icc
    ((690989 : ℝ) ^ 2 - (901 / 10000 : ℝ) / 16)
    ((1381978 : ℝ) ^ 2 - (901 / 10000 : ℝ) / 16)

noncomputable def poweredResidual20175
    (q : ℕ → ℝ) (k : ℕ) (U : ℝ) : ℂ :=
  residualQ20175 q U ^ k

/-- Claim 20175: with the literal finite residual and first dyadic block,
the constant phase carrier has the exact quadratic energy, its stated
minimizer, and the corresponding signed-power Sobolev consequence. -/
def constantCarrierPhaseEnergyQuadraticCore_claim20175
    (q : ℕ → ℝ) (k : ℕ) : Prop :=
  1 ≤ k ∧
    (∀ U ∈ firstOpenBlock20175,
      ContDiffWithinAt ℝ 1 (residualQ20175 q)
        (firstOpenBlock20175 : Set ℝ) U) ∧
    let J : Set ℝ := firstOpenBlock20175
    let ℓ : ℝ := 3 * (690989 : ℝ) ^ 2
    let Q : ℝ → ℂ := residualQ20175 q
    let F : ℝ → ℂ := poweredResidual20175 q k
    let A : ℝ := ∫ U in J, ‖Q U‖ ^ (2 * k)
    let D : ℝ :=
      (k : ℝ) ^ 2 *
        ∫ U in J, ‖Q U‖ ^ (2 * k - 2) *
          ‖derivWithin Q J U‖ ^ 2
    let K : ℝ :=
      (k : ℝ) *
        ∫ U in J,
          ‖Q U‖ ^ (2 * k - 2) *
            Complex.im (derivWithin Q J U * star (Q U))
    (volume J = ENNReal.ofReal ℓ ∧
      ℓ > 0 ∧
      (∀ c : ℝ,
        ∫ U in J,
            ‖derivWithin F J U - Complex.I * (c : ℂ) * F U‖ ^ 2 =
          D - 2 * c * K + c ^ 2 * A) ∧
      (A > 0 →
        (∀ c : ℝ,
          D - K ^ 2 / A ≤
            ∫ U in J,
              ‖derivWithin F J U - Complex.I * (c : ℂ) * F U‖ ^ 2) ∧
        (∫ U in J,
            ‖derivWithin F J U - Complex.I * ((K / A : ℝ) : ℂ) * F U‖ ^ 2 =
          D - K ^ 2 / A) ∧
      (A > 0 →
        K ^ 2 ≤ A * D ∧
          sSup ((fun U => ‖F U‖ ^ 2) '' J) ≤
            A / ℓ + 2 * Real.sqrt (A * (D - K ^ 2 / A)))))

end

end MathlibPlus.Open.Analysis.R0344.Claim20175
