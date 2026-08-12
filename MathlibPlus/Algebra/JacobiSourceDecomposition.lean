import Mathlib

namespace MathlibPlus.Algebra.JacobiSource

/-!
Formalization of admitted claim 8597 (locator `K-0105`).  The source's
Cholesky symbols are written as arbitrary real entries; this declaration
captures the exact local stagger/energy identity and does not assert the
separate positivity or Jacobi-factorization hypotheses from K-0105.
-/

/-- The Jacobi source is the half-difference of the stagger plus half the
nonnegative adjacent-variation energy. -/
theorem sourceDecomposition_claim8597 (rPrev sCurr rCurr sNext : ℝ) :
    let source := sCurr * (sCurr - rPrev) + rCurr * (rCurr - sNext)
    let stagger := sCurr ^ 2 - rPrev ^ 2
    let nextStagger := sNext ^ 2 - rCurr ^ 2
    let energy := (sCurr - rPrev) ^ 2 + (rCurr - sNext) ^ 2
    0 ≤ energy ∧
      source = (1 : ℝ) / 2 * (stagger - nextStagger) +
        (1 : ℝ) / 2 * energy := by
  dsimp
  constructor
  · positivity
  · ring

end MathlibPlus.Algebra.JacobiSource
