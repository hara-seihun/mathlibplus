import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0082

noncomputable section

/-- Claim 17779: the displayed Green operator acts on `k` by the quadratic
polynomial in `r = exp (2t)`. -/
def claim17779_exactGreenOperatorAction
    (k Lk p : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    Lk t = -iteratedDeriv 2 k t + (1 / 4 : ℝ) * k t ∧
      Lk t =
        (-4 * Real.pi ^ 2 * (Real.exp (2 * t)) ^ 2 +
          14 * Real.pi * Real.exp (2 * t) - 6) * k t ∧
      p (Real.exp (2 * t)) =
        -4 * Real.pi ^ 2 * (Real.exp (2 * t)) ^ 2 +
          14 * Real.pi * Real.exp (2 * t) - 6

/-- Claim 17780: the ordered two-point Green compound is the evaluation
 determinant. -/
def claim17780_twoPointGreenCompoundDeterminant
    (k Lk : ℝ → ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ,
    let evaluation : Matrix (Fin 2) (Fin 2) ℝ := fun i j ↦
      if i = 0 then
        if j = 0 then k t₁ else Lk t₁
      else if j = 0 then k t₂ else Lk t₂
    C t₁ t₂ = k t₁ * Lk t₂ - k t₂ * Lk t₁ ∧
      C t₁ t₂ = Matrix.det evaluation

/-- Claim 17781: the exact factorization of the two-point compound. -/
def claim17781_exactTwoPointCompoundFactorization
    (k : ℝ → ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ,
    C t₁ t₂ =
      k t₁ * k t₂ *
        (Real.exp (2 * t₂) - Real.exp (2 * t₁)) *
        (14 * Real.pi - 4 * Real.pi ^ 2 *
          (Real.exp (2 * t₁) + Real.exp (2 * t₂)))

/-- Claim 17782: ordered points meet exactly one affine sign wall. -/
def claim17782_exactlyOneAffineSignWall
    (k : ℝ → ℝ) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ, t₁ < t₂ →
    0 < k t₁ * k t₂ ∧
    0 < Real.exp (2 * t₂) - Real.exp (2 * t₁) ∧
    C t₁ t₂ =
      k t₁ * k t₂ *
        (Real.exp (2 * t₂) - Real.exp (2 * t₁)) *
        (14 * Real.pi - 4 * Real.pi ^ 2 *
          (Real.exp (2 * t₁) + Real.exp (2 * t₂))) ∧
    (C t₁ t₂ = 0 ↔
      Real.exp (2 * t₁) + Real.exp (2 * t₂) = 7 / (2 * Real.pi)) ∧
    (0 < C t₁ t₂ ↔
      Real.exp (2 * t₁) + Real.exp (2 * t₂) < 7 / (2 * Real.pi)) ∧
    (C t₁ t₂ < 0 ↔
      Real.exp (2 * t₁) + Real.exp (2 * t₂) > 7 / (2 * Real.pi))

end

end MathlibPlus.Open.NewResearch2.R0082
