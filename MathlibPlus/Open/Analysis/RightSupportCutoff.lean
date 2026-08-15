import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The rescaled positive sampling kernel from the admitted packet. -/
noncomputable def Kq (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) * ∑' n : ℕ, if 1 ≤ n then q ((n : ℝ) * Real.exp x) else 0

/-- If a source is supported in the exponential interval and vanishes at its
right endpoint, its positive sampling kernel vanishes to the right of that
endpoint. -/
def rightSupportCutoff : Prop :=
  ∀ (q : ℝ → ℝ) (L : ℝ),
    Function.support q ⊆ Set.Icc (-(Real.exp L)) (Real.exp L) →
    q (Real.exp L) = 0 →
    ∀ x : ℝ, L ≤ x → Kq q x = 0

end MathlibPlus.Open.Analysis
