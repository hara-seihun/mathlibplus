import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0232Claim19051

noncomputable section

/-- The growth condition for an entire function to have order at most one. -/
def entireOrderAtMostOne (f : ℂ → ℂ) : Prop :=
  ∀ ρ : ℝ, 1 < ρ →
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ,
        ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ)

/-- The lower-growth half of exact entire-function order one. -/
def entireOrderAtLeastOne (f : ℂ → ℂ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ C : ℝ, ∃ z : ℂ,
      Real.exp (C * (1 + ‖z‖) ^ ρ) < ‖f z‖

def entireOrderExactlyOne (f : ℂ → ℂ) : Prop :=
  entireOrderAtMostOne f ∧ entireOrderAtLeastOne f

/-- The reflected exponential factor. -/
def reflectedB (a r : ℝ) : ℂ → ℂ :=
  fun z =>
    (1 + (r : ℂ) * Complex.exp ((a : ℂ) * z)) *
      (1 + (r : ℂ) * Complex.exp (-((a : ℂ) * z)))

/-- Claim 19051: the exact reflected factor is even, real on the real axis,
conjugation-symmetric, entire, of the admitted order, and has the displayed
positive exponential-polynomial coefficients when `r` is positive. -/
def claim19051 : Prop :=
  ∀ (a r : ℝ),
    let B := reflectedB a r
    Even B ∧
      (∀ z : ℂ, B (starRingEnd ℂ z) = starRingEnd ℂ (B z)) ∧
      (∀ x : ℝ, (B (x : ℂ)).im = 0) ∧
      Differentiable ℂ B ∧
      entireOrderAtMostOne B ∧
      (a ≠ 0 → 0 < r → entireOrderExactlyOne B) ∧
      (∀ z : ℂ,
        B z =
          ((1 + r ^ 2 : ℝ) : ℂ) +
            (r : ℂ) * Complex.exp ((a : ℂ) * z) +
            (r : ℂ) * Complex.exp (-((a : ℂ) * z))) ∧
      (0 < r →
        0 < (1 : ℝ) ∧ 0 < r ^ 2 ∧ 0 < r ∧ 0 < r)

end
end MathlibPlus.Open.ResearchFormalization.R0232Claim19051
