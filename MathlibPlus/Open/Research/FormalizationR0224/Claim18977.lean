import MathlibPlus.Open.Research.FrobeniusPurity18978

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationR0224

noncomputable section

private def positiveFormalEulerExponents18977 : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ q : ℕ, 0 < q ∧
      MathlibPlus.Open.Analysis.positiveEulerExponent m = (q : ℝ)

private def reciprocalNumerator18977 (u : ℂ) : ℂ :=
  MathlibPlus.Open.Analysis.positiveEulerNumerator u

private def reciprocalSymmetry18977 : Prop :=
  ∀ u : ℂ, u ≠ 0 →
    reciprocalNumerator18977 u =
      9 * u ^ 2 * reciprocalNumerator18977 (1 / (9 * u))

private def polarizedPurity18977 : Prop :=
  ∀ u : ℂ,
    reciprocalNumerator18977 u = 0 →
      ‖u⁻¹‖ = Real.sqrt 9

/-- Claim 18977: the fixed reciprocal polynomial has positive integral formal
closed-point exponents in every positive degree, while failing the required
polarized purity conclusion. -/
def claim18977 : Prop :=
  positiveFormalEulerExponents18977 ∧
    reciprocalSymmetry18977 ∧
    ¬ polarizedPurity18977

end

end MathlibPlus.Open.Research.FormalizationR0224
