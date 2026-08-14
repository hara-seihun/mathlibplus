import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The arithmetic nodes used by the Newton divided differences in Claim 1643. -/
def arithmeticNode (a : ℝ) (r : ℕ) : ℝ := a + (r : ℝ)

/-- The divided difference on the arithmetic nodes `a, a + 1, ..., a + k`.

This is the usual explicit barycentric formula for a divided difference. -/
noncomputable def arithmeticDividedDifference
    (a : ℝ) (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) (fun i =>
    f (arithmeticNode a i) /
      Finset.prod ((Finset.range (k + 1)).erase i) (fun j =>
        arithmeticNode a i - arithmeticNode a j))

/-- The rising factorial `(2a + e)_t` appearing in Claim 1643. -/
noncomputable def arithmeticRisingFactorial
    (a : ℝ) (e t : ℕ) : ℝ :=
  Finset.prod (Finset.range t) (fun r =>
    2 * a + (e : ℝ) + (r : ℝ))

/-- The polynomial `F_e` from Claim 1643. -/
noncomputable def arithmeticNewtonPolynomial
    (a : ℝ) (e : ℕ) (x : ℝ) : ℝ :=
  Finset.prod (Finset.range e) (fun r =>
      x ^ 2 - (arithmeticNode a r) ^ 2)
    - Finset.prod (Finset.range e) (fun r =>
        -((arithmeticNode a r) ^ 2))

/-- Claim 1643: the arithmetic Newton-tail identity. -/
def arithmeticNewtonTailIdentity
    (a : ℝ) (e t : ℕ) : Prop :=
  arithmeticDividedDifference a (e + t) (arithmeticNewtonPolynomial a e) /
      arithmeticDividedDifference a e (arithmeticNewtonPolynomial a e)
    = (Nat.choose e t : ℝ) / arithmeticRisingFactorial a e t

end MathlibPlus.Open.Analysis
