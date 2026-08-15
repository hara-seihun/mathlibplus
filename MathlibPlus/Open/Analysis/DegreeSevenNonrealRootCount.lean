import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The exact truncation used in the admitted degree-seven root-count claim. -/
noncomputable def qTruncation (q : ℝ) (n : ℕ) : Polynomial ℂ :=
  (Finset.range (n + 1)).sum (fun k =>
    Polynomial.monomial k
      (↑(q ^ (Nat.choose k 2) / (Nat.factorial k : ℝ)) : ℂ))

/-- The theta-edge parameter appearing in the admitted scaling. -/
noncomputable def thetaEdgeGamma (n : ℕ) : ℝ :=
  1 / 2 + 1 / Real.sqrt n

/-- The exact theta-edge value of q at size n. -/
noncomputable def thetaEdgeQ (n : ℕ) : ℝ :=
  Real.exp (-2 * thetaEdgeGamma n / n)

/-- At the displayed theta-edge scaling, the degree-seven truncation has six
nonreal roots and exactly one real root. -/
noncomputable def degreeSevenNonrealRootCount : Prop :=
  let p := qTruncation (thetaEdgeQ 7) 7
  (p.roots.filter (fun z => z.im ≠ 0)).card = 6 ∧
    (p.roots.filter (fun z => z.im = 0)).card = 1

end MathlibPlus.Open.Analysis
