import Mathlib

<<<<<<< ours
namespace MathlibPlus.Open.ResearchFormalizationBatch.Algebra

/-- A divisibility-greatest common divisor, which is the UFD notion used by the
one-marker primitive-content split. -/
def IsDivisibilityGcd {R : Type*} [CommMonoidWithZero R]
    (h a b : R) : Prop :=
  h ∣ a ∧ h ∣ b ∧ ∀ d : R, d ∣ a → d ∣ b → d ∣ h

/-- Exact one-marker primitive-content descent over the coefficient UFD. -/
def claim_27595 {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] : Prop :=
  ∀ (a b h a' b' : R) (F : Polynomial R),
    F = Polynomial.C b + Polynomial.C a * Polynomial.X →
    (∀ r : R, F ≠ Polynomial.C r) →
    IsDivisibilityGcd h a b →
    h * a' = a →
    h * b' = b →
    a' ≠ 0 ∧
      Polynomial.IsPrimitive (Polynomial.C b' + Polynomial.C a' * Polynomial.X) ∧
      Irreducible (Polynomial.C b' + Polynomial.C a' * Polynomial.X)

end MathlibPlus.Open.ResearchFormalizationBatch.Algebra
=======
namespace MathlibPlus.Open.ResearchAlgebraBatch

noncomputable section

private def anchoredBezoutB2 (h₀ h₁ h₂ h₃ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![h₀ * h₁, 2 * h₀ * h₂],
    ![2 * h₀ * h₂, h₁ * h₂ + 3 * h₀ * h₃]]

/-- Claim 17892: the rank-two anchored Bezout section has the displayed
coefficient matrix. -/
def claim17892_rankTwoAnchoredBezoutSection : Prop :=
  ∀ h₀ h₁ h₂ h₃ : ℝ,
    anchoredBezoutB2 h₀ h₁ h₂ h₃ =
      ![![h₀ * h₁, 2 * h₀ * h₂],
        ![2 * h₀ * h₂, h₁ * h₂ + 3 * h₀ * h₃]]

/-- Claim 17894: the determinant factors in successive coefficient ratios. -/
def claim17894_ratioCoordinateDeterminantFactorization : Prop :=
  ∀ h₀ h₁ h₂ h₃ a b c : ℝ,
    h₀ ≠ 0 → h₁ ≠ 0 → h₂ ≠ 0 →
      a = h₁ / h₀ → b = h₂ / h₁ → c = h₃ / h₂ →
      Matrix.det (anchoredBezoutB2 h₀ h₁ h₂ h₃) =
        h₀ ^ 4 * a ^ 2 * b * (a - 4 * b + 3 * c)

/-- Claim 17895: under positive initial ratios, determinant positivity is
exactly the stated discrete ratio-curvature inequality. -/
def claim17895_discreteRatioCurvaturePositivity : Prop :=
  ∀ h₀ h₁ h₂ h₃ a b c : ℝ,
    h₀ ≠ 0 → h₁ ≠ 0 → h₂ ≠ 0 →
      a = h₁ / h₀ → b = h₂ / h₁ → c = h₃ / h₂ →
      0 < h₀ → 0 < a → 0 < b →
      (Matrix.det (anchoredBezoutB2 h₀ h₁ h₂ h₃) > 0 ↔
        a - 4 * b + 3 * c > 0) ∧
      (a - 4 * b + 3 * c > 0 ↔ a - b > 3 * (b - c))

/-- Claim 17896: with positive successive gaps, the same criterion is the
ratio inequality. -/
def claim17896_positiveGapQuotientCriterion : Prop :=
  ∀ (a b c : ℝ),
    b > c →
      (a - 4 * b + 3 * c > 0 ↔ (a - b) / (b - c) > 3) ∧
      (a - b > 3 * (b - c) ↔ (a - b) / (b - c) > 3)

end

end MathlibPlus.Open.ResearchAlgebraBatch
>>>>>>> theirs
