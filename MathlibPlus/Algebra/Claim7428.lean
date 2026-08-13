import Mathlib

namespace MathlibPlus.Algebra.Claim7428

/-!
The source identifies two reciprocal exponential spectral points.  The exact
algebraic content that is independent of the source's undefined `K_q` notation
is recorded here; the latter notation is left for fidelity review rather than
being assigned an analytic or difference-operator meaning.
-/

/-- The reciprocal exponential quadratic factors at the two spectral points. -/
theorem spectralQuadratic_factorization_claim7428 (t x : ℝ) :
    x ^ 2 - 2 * Real.cosh t * x + 1 =
      (x - Real.exp (-t)) * (x - Real.exp t) := by
  rw [Real.cosh_eq]
  ring_nf
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  ring

/-- `exp (-t)` and `exp t` are roots of the reciprocal quadratic from claim
7428. -/
theorem spectralQuadratic_roots_claim7428 (t : ℝ) :
    let lambdaMinus := Real.exp (-t)
    let lambdaPlus := Real.exp t
    (lambdaMinus ^ 2 - 2 * Real.cosh t * lambdaMinus + 1 = 0) ∧
      (lambdaPlus ^ 2 - 2 * Real.cosh t * lambdaPlus + 1 = 0) := by
  constructor
  · rw [spectralQuadratic_factorization_claim7428]
    ring
  · rw [spectralQuadratic_factorization_claim7428]
    ring

end MathlibPlus.Algebra.Claim7428
