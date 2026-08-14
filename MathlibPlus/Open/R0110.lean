import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.R0110

private def hurwitzTail (M : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, Real.rpow (((M + 1 + n : ℕ) : ℝ)) (-s)

private def completion (s : ℝ) : ℝ :=
  s * (1 - s) * Real.rpow Real.pi (-s / 2) * Real.Gamma (1 + s / 2)

/-- Green--gamma completion cancels the rational pole algebraically. -/
def claim_18022 : Prop :=
  ∀ (M : ℕ) (s : ℝ),
    s ≠ 0 → s ≠ 1 →
    Summable (fun n : ℕ => Real.rpow
      (((M + 1 + n : ℕ) : ℝ)) (-s)) →
    completion s *
        (Real.rpow (M : ℝ) (1 - s) / (s * (s - 1)) -
          hurwitzTail M s / s) =
      -Real.rpow (M : ℝ) (1 - s) *
          Real.rpow Real.pi (-s / 2) * Real.Gamma (1 + s / 2) -
        (1 - s) * Real.rpow Real.pi (-s / 2) *
          Real.Gamma (1 + s / 2) * hurwitzTail M s

end MathlibPlus.Open.R0110
