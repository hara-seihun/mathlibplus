import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2

noncomputable section

open scoped Classical

private noncomputable def thetaW (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    ∑' n : ℕ,
      if 1 ≤ n then
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
      else 0

private noncomputable def thetaPhi (u : ℝ) : ℝ :=
  deriv (deriv thetaW) u - (1 / 4 : ℝ) * thetaW u

private noncomputable def thetaPhiSecond (u : ℝ) : ℝ :=
  deriv (deriv thetaPhi) u

private def thetaMixedDet (u v : ℝ) : ℝ :=
  thetaW u * thetaPhiSecond v - thetaW v * thetaPhiSecond u

/-- Claim 12030: the theta primitive and completed function have the stated
operator relation and second-derivative expansion. -/
def claim12030 : Prop :=
  (∀ u : ℝ,
      thetaPhi u = deriv (deriv thetaW) u - (1 / 4 : ℝ) * thetaW u) ∧
    (∀ u : ℝ,
      thetaPhiSecond u = iteratedDeriv 4 thetaW u -
        (1 / 4 : ℝ) * iteratedDeriv 2 thetaW u)

/-- Claim 12031: every theta shell derivative is governed by the displayed
polynomial recurrence. -/
def claim12031 : Prop :=
  ∃ P : ℕ → Polynomial ℝ,
    P 0 = 1 ∧
      (∀ d : ℕ,
        P (d + 1) =
          (Polynomial.C (1 / 2 : ℝ) - Polynomial.C 2 * Polynomial.X) * P d +
            Polynomial.C 2 * Polynomial.X * Polynomial.derivative (P d)) ∧
        (∀ d n : ℕ, ∀ u : ℝ,
          let y : ℝ := Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)
          iteratedDeriv d
              (fun v : ℝ => Real.exp (v / 2 -
                Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * v))) u =
            Polynomial.eval y (P d) * Real.exp (u / 2 - y))

/-- Claim 12032: the ordered rational rank-two mixed determinant is strictly
negative with the certified enclosure. -/
def claim12032 : Prop :=
  let u₁ : ℝ := 1 / 100
  let u₂ : ℝ := 1 / 20
  let value : ℝ := thetaMixedDet u₁ u₂
  value < 0 ∧
    |value -
        (-0.1096918684923246350624090653947063759361286348807 : ℝ)| <
      (8.75 : ℝ) * (10 : ℝ)⁻¹ ^ 104

/-- Claim 12033: strict negativity persists on an open ordered chamber. -/
def claim12033 : Prop :=
  let u₁ : ℝ := 1 / 100
  let u₂ : ℝ := 1 / 20
  ContinuousAt (fun p : ℝ × ℝ => thetaMixedDet p.1 p.2) (u₁, u₂) ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ,
        u < v → |u - u₁| < δ → |v - u₂| < δ → thetaMixedDet u v < 0

/-- Claim 12035: the literal mixed density is not pointwise nonnegative on
the ordered rank-two chamber. -/
def claim12035 : Prop :=
  (∃ u v : ℝ, u < v ∧ thetaMixedDet u v < 0) ∧
    (¬ ∀ u v : ℝ, u < v → 0 ≤ thetaMixedDet u v)

end
end MathlibPlus.Open.NewResearch2
