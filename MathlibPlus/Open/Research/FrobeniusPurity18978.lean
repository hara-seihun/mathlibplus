import MathlibPlus.Open.Analysis.PositiveCounterfeitBatch

namespace MathlibPlus.Open.Research.FormalizationR0224

noncomputable section

private def counterfeitNumerator (u : ℂ) : ℂ :=
  1 + 7 * u + 9 * u ^ 2

private def positiveFormalEulerExponents : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ q : ℕ,
      0 < q ∧
        MathlibPlus.Open.Analysis.positiveEulerExponent m = (q : ℝ)

private def counterfeitReciprocity : Prop :=
  ∀ u : ℂ, u ≠ 0 →
    counterfeitNumerator u =
      9 * u ^ 2 * counterfeitNumerator (1 / (9 * u))

/-- The weight-nine purity conclusion forced by a positive Rosati
polarization: every reciprocal root of the fixed polynomial has modulus
`sqrt 9`. -/
private def rosatiPurityConclusion : Prop :=
  ∀ u : ℂ,
    counterfeitNumerator u = 0 →
      ‖u⁻¹‖ = Real.sqrt 9

/-- Claim 18978: the fixed reciprocal polynomial has positive integral formal
closed-point exponents and reciprocity, yet those data do not yield the
Rosati/purity conclusion required at weight nine. -/
def counterfeitLacksPolarizedPurity18978 : Prop :=
  positiveFormalEulerExponents ∧
    counterfeitReciprocity ∧
      ¬rosatiPurityConclusion

end

end MathlibPlus.Open.Research.FormalizationR0224
