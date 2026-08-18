import MathlibPlus.Open.ResearchFormalization.R0232Claim19051

namespace MathlibPlus.Open.ResearchFormalization.R0232Claims19053_19054

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0232Claim19051

/-- Claim 19053: the exact zero set is the two reflected integer lattices. -/
def claim19053 : Prop :=
  ∀ (a r : ℝ),
    0 < a → 0 < r →
      let B := reflectedB a r
      ∀ z : ℂ,
        B z = 0 ↔
          ∃ k : ℤ, ∃ ε : ℤ,
            (ε = -1 ∨ ε = 1) ∧
              z =
                (((ε : ℂ) * Complex.log (r : ℂ) +
                    ((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I) /
                  (a : ℂ))

/-- Claim 19054: the imaginary-axis zero balance is exactly `r = 1`,
and the unbalanced zeros have the stated real-part displacement. -/
def claim19054 : Prop :=
  ∀ (a r : ℝ),
    0 < a → 0 < r →
      let B := reflectedB a r
      ((∀ z : ℂ, B z = 0 → z.re ≠ 0) ↔ r ≠ 1) ∧
        (r = 1 → ∀ z : ℂ, B z = 0 → z.re = 0) ∧
        (r ≠ 1 →
          ∀ z : ℂ, B z = 0 →
            (z.re = Real.log r / a ∨ z.re = -(Real.log r / a)) ∧
              z.re ≠ 0)

end
end MathlibPlus.Open.ResearchFormalization.R0232Claims19053_19054
