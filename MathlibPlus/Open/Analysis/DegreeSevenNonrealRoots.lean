import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The truncation polynomial appearing in the admitted claim. -/
def truncExp (q : ℂ) (n : ℕ) : Polynomial ℂ :=
  (Finset.range (n + 1)).sum (fun k =>
    Polynomial.C (q ^ (k.choose 2) * (k.factorial : ℂ)⁻¹) * Polynomial.X ^ k)

/-- The displayed theta-edge parameter, with `n⁻¹ᐟ²` written using the square root. -/
def thetaEdgeQ (n : ℕ) : ℂ :=
  Complex.ofReal (Real.exp
    (-2 * ((1 / 2 : ℝ) + (1 / Real.sqrt (n : ℝ))) / (n : ℝ)))

/-- At the displayed edge scaling, the degree-seven truncation has six
nonreal roots and exactly one real root. -/
def degreeSevenNonrealRootCount : Prop :=
  let p := truncExp (thetaEdgeQ 7) 7
  (p.roots.filter (fun z => z.im ≠ 0)).card = 6 ∧
    (p.roots.filter (fun z => z.im = 0)).card = 1

end

end MathlibPlus.Open.Analysis
