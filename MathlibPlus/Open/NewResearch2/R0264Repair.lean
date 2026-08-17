import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0264Repair

noncomputable section

/-- The first-shell boundary quantity from the modular integration-by-parts
packet. -/
def shellBoundaryFactor (lam u : ℝ) : ℝ :=
  1 + u / 2 - 2 * lam * u * Real.exp (2 * u)

/-- The zeroth diagonal Taylor coefficient of the locally transformed kernel. -/
def zerothDiagonalCoefficient (alpha lam u : ℝ) : ℝ :=
  1 / 2 + shellBoundaryFactor lam u *
    (alpha * u ^ 2 / 8 - 1 / 4)

/-- Pointwise positivity of the zeroth diagonal coefficient on the original
shell/age parameter range. -/
def pointwiseZerothDiagonalNonnegative : Prop :=
  ∀ lam u : ℝ, Real.pi ≤ lam → 0 ≤ zerothDiagonalCoefficient (1 / 4 : ℝ) lam u

/-- Claim 19309: the order-zero, first-shell, age-three test is already
strictly negative for every arithmetic shell parameter, so pointwise
positivity on the original measure fails without using higher orders, shells,
or mixed ages. -/
def claim19309_weakestLocalObstruction : Prop :=
  (∀ lam : ℝ, Real.pi ≤ lam →
    zerothDiagonalCoefficient (1 / 4 : ℝ) lam 3 < 0) ∧
    ¬ pointwiseZerothDiagonalNonnegative

end

end MathlibPlus.Open.NewResearch2.R0264Repair
