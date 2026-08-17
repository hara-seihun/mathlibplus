import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0232Claim19055

noncomputable section

def reflectedB (a r : ℝ) : ℂ → ℂ :=
  fun z =>
    ((1 + r ^ 2 : ℝ) : ℂ) +
      (r : ℂ) * Complex.exp ((a : ℂ) * z) +
      (r : ℂ) * Complex.exp (-((a : ℂ) * z))

/-- Claim 19055: at prime-frequency scale `a = log p` and `r = p^theta`,
every zero of the exact reflected factor has real part `+theta` or
`-theta`, so its displacement from the imaginary axis is exactly `|theta|`. -/
def claim19055 : Prop :=
  ∀ (p θ : ℝ),
    1 < p →
      let a : ℝ := Real.log p
      let r : ℝ := Real.rpow p θ
      let B := reflectedB a r
      ∀ z : ℂ,
        B z = 0 →
          (z.re = θ ∨ z.re = -θ) ∧
            |z.re| = |θ| ∧
            (z.re ≠ 0 ↔ θ ≠ 0)

end
end MathlibPlus.Open.ResearchFormalization.R0232Claim19055
