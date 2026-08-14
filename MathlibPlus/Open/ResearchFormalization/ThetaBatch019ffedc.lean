import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

noncomputable section

def chebyshevTheta (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (Nat.floor x + 1))
    (fun p => if Nat.Prime p then Real.log (p : ℝ) else 0)

def exponentSixtyFourThetaDifference (x : ℝ) : ℝ :=
  chebyshevTheta (x + 64 * Real.rpow x (63 / 64 : ℝ)) -
    chebyshevTheta x

/-- Claim 1371. -/
def largeXPositiveThetaDifference : Prop :=
  ∀ x : ℝ, Real.exp 1946 ≤ x →
    exponentSixtyFourThetaDifference x > 0

/-- Claim 1373. -/
def lowRangeThetaSplice : Prop :=
  let L₀ : ℝ :=
    64 * Real.log
      (64 * (251949000000 : ℝ) *
        (1 - 1 / (251949000000 : ℝ))^2)
  L₀ > 1946 ∧
    ∀ x : ℝ,
      (4 : ℝ) * 10^18 ≤ x → x ≤ Real.exp L₀ →
        exponentSixtyFourThetaDifference x > 0

end
end MathlibPlus.Open.ResearchFormalization
