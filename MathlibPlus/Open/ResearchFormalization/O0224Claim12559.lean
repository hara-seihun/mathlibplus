import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0224Claim12559

/-- Claim 12559: the literal second-logarithmic-jet derivative and multiplier
identities, with A=a' and F=pa-a²/2. -/
def claim12559 : Prop :=
  ∀ (p : ℝ) (a : ℝ → ℝ),
    (∀ x, HasDerivAt a (deriv a x) x) →
      (∀ x,
        HasDerivAt (fun y => p * a y - (a y) ^ 2 / 2)
          ((p - a x) * deriv a x) x) ∧
      (∀ x,
        (p - a x) * (p * a x - (a x) ^ 2 / 2) - deriv (deriv a) x =
          (a x * (a x - p) * (a x - 2 * p) -
            2 * deriv (deriv a) x) / 2)

end MathlibPlus.Open.ResearchFormalization.O0224Claim12559
