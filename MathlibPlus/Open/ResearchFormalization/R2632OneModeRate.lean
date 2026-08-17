import MathlibPlus.Open.ResearchFormalization.R2632Claim42992

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2632OneModeRate

noncomputable section

/-- The scalar one-mode rate in Claim 42987. -/
def oneModeRate42987 (d : ℝ) (a : ℂ) : ℝ :=
  2 * (a - 1).re +
    d * (1 + Real.log (‖a - 1‖ ^ 2 / d))

/-- The explicit exterior-square two-mode channel whose normalized rate is
compared with the two one-mode rates. -/
def exteriorSquarePairChannel42987
    (d : ℝ) (a b : ℂ) (x : ℝ) : ℝ :=
  let r := Nat.floor (d * x)
  x ^ r / (Nat.factorial r : ℝ) *
    ‖(a - b) ^ 2 *
        ((a - 1) * (b - 1)) ^ r *
          Complex.exp ((a + b - 2) * x)‖

def exteriorSquarePairRate42987 (d : ℝ) (a b : ℂ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => x⁻¹ *
      Real.log (1 + exteriorSquarePairChannel42987 d a b x))
    Filter.atTop

/-- Claim 42987: the scalar convex/logarithmic one-mode inequality has the
stated equality condition, and the explicit exterior-square pair rate is the
average of the two one-mode rates. -/
def oneModeRateInequalityAndPairAverage_claim42987 : Prop :=
  (∀ (d : ℝ) (a : ℂ), 0 < d → a ≠ 1 →
    oneModeRate42987 d a ≤ ‖a‖ ^ 2 - 1 ∧
      (oneModeRate42987 d a = ‖a‖ ^ 2 - 1 ↔
        d = ‖a - 1‖ ^ 2)) ∧
    (∀ (d : ℝ) (a b : ℂ),
      0 < d → a ≠ 1 → b ≠ 1 → a ≠ b →
        exteriorSquarePairRate42987 d a b =
          (oneModeRate42987 d a + oneModeRate42987 d b) / 2)

end

end MathlibPlus.Open.ResearchFormalization.R2632OneModeRate
