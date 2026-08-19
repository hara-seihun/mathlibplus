import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

/-- Claim 10869: the displayed functional-equation-symmetric quartic has its
four zeros in the open critical strip and off the critical line. -/
def hurwitzStableFunctionalEquationCounterfeit : Prop :=
  let A : ℂ → ℂ := fun z =>
    ((z + (1 / 10 : ℂ)) ^ 2 + 1) *
      ((z + (2 / 5 : ℂ)) ^ 2 + 1)
  let ℒ : ℂ → ℂ := fun s => A ((s - 1) / 2)
  (∀ z : ℂ, A (-z - (1 / 2 : ℂ)) = A z) ∧
    (∀ s : ℂ, ℒ (1 - s) = ℒ s) ∧
    (∀ s : ℂ,
      ℒ s = 0 ↔
        s = 1 / 5 + 2 * Complex.I ∨
          s = 1 / 5 - 2 * Complex.I ∨
          s = 4 / 5 + 2 * Complex.I ∨
          s = 4 / 5 - 2 * Complex.I) ∧
    (∀ s : ℂ, ℒ s = 0 →
      0 < s.re ∧ s.re < 1 ∧ s.re ≠ (1 / 2 : ℝ))

end

end MathlibPlus.Analysis
