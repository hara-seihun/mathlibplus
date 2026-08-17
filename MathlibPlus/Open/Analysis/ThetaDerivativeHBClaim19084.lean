import MathlibPlus.Analysis.ThetaShellSummandClaim19068

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim19084

noncomputable section

/-- The literal positive-half-line theta source. -/
def literalPhi : ℝ → ℝ := fun u ↦
  ∑' m : {m : ℕ // 0 < m},
    MathlibPlus.Analysis.thetaShellSummand m.1 u

/-- The transform H_t used by the derivative Hermite--Biehler claim. -/
def literalHeatTransform (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ici (0 : ℝ),
    Complex.exp (((t * u ^ 2 : ℝ) : ℂ)) *
      (literalPhi u : ℂ) * Complex.cos (z * (u : ℂ))

/-- The strict Hermite--Biehler inequality in the upper half-plane. -/
def hermiteBiehler (E Esharp : ℂ → ℂ) : Prop :=
  (∀ z : ℂ,
    Esharp z = starRingEnd ℂ (E (starRingEnd ℂ z))) ∧
    ∀ z : ℂ, 0 < z.im → ‖Esharp z‖ < ‖E z‖

/-- Real zeros after removal of a common real entire factor.  The factor is
required to divide both F and F', to have only real zeros, and to leave a
quotient with only real zeros. -/
def realZerosAfterCommonRealFactors (F : ℂ → ℂ) : Prop :=
  ∃ G Q R : ℂ → ℂ,
    Differentiable ℂ G ∧
      (∀ x : ℝ, (G (x : ℂ)).im = 0) ∧
      (∃ z : ℂ, G z ≠ 0) ∧
      (∀ z : ℂ, G z = 0 → z.im = 0) ∧
      Differentiable ℂ Q ∧
      Differentiable ℂ R ∧
      (∀ z : ℂ, F z = G z * Q z) ∧
      (∀ z : ℂ, deriv F z = G z * R z) ∧
      (∃ z : ℂ, Q z ≠ 0) ∧
      (∀ z : ℂ, Q z = 0 → z.im = 0)

/-- Claim 19084: for F = H_τ and a > 0, the derivative pair has the stated
sharp, modulus identity, and strict Hermite--Biehler/real-zero equivalence. -/
def derivativeHermiteBiehlerEquivalence_claim19084 : Prop :=
  ∀ τ a : ℝ, 0 < a →
    let F : ℂ → ℂ := literalHeatTransform τ
    let F' : ℂ → ℂ := fun z => deriv F z
    let E : ℂ → ℂ := fun z => F z + Complex.I * (a : ℂ) * F' z
    let Esharp : ℂ → ℂ := fun z => F z - Complex.I * (a : ℂ) * F' z
    (∀ z : ℂ,
      Esharp z = starRingEnd ℂ (E (starRingEnd ℂ z))) ∧
      (∀ z : ℂ,
        ‖E z‖ ^ 2 - ‖Esharp z‖ ^ 2 =
          -4 * a * ‖F z‖ ^ 2 * (F' z / F z).im) ∧
      (hermiteBiehler E Esharp ↔ realZerosAfterCommonRealFactors F)

end

end MathlibPlus.Open.Analysis.Claim19084
