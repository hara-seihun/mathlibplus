import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ReflectedAtomBatch

/-- Claim 14497: the reflected adversarial atom and its imbalance parameter. -/
def reflectedAdversarialAtom14497 : Prop :=
  ∀ (lam : ℝ) (r : ℝ), lam ≠ 0 → 0 < r →
    ∃ (B : ℂ → ℂ) (θ : ℝ),
      (∀ z : ℂ,
        B z = (1 + r * Complex.exp (lam * z)) *
          (1 + r * Complex.exp (-lam * z))) ∧
      θ = Real.log r / lam

/-- Claim 14498: the reflected atom has exactly two vertical zero lines, with
balanced amplitude precisely the central-line case. -/
def reflectedAtomZeroLines14498 : Prop :=
  ∀ (lam r : ℝ), 0 < lam → 0 < r →
    let θ := Real.log r / lam
    let B : ℂ → ℂ := fun z =>
      (1 + r * Complex.exp (lam * z)) *
        (1 + r * Complex.exp (-lam * z))
    (∀ z : ℂ,
      B z = 0 ↔
        ((z.re = -θ ∧ ∃ k : ℤ, z.im = ((2 * k + 1 : ℤ) : ℝ) * Real.pi / lam) ∨
         (z.re = θ ∧ ∃ k : ℤ, z.im = ((2 * k + 1 : ℤ) : ℝ) * Real.pi / lam))) ∧
    ((r = 1 ↔ θ = 0) ∧
      (r = 1 → ∀ z : ℂ, B z = 0 → z.re = 0))

end MathlibPlus.Open.Analysis.ReflectedAtomBatch
