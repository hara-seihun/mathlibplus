import Mathlib

namespace MathlibPlus.Analysis.Claim9538

noncomputable section

/-- The deformed exponential from claim 9538, with its stated parameter
range represented by a subtype.  No convergence or analytic property is
asserted here; this declaration records the displayed series. -/
def deformedExponential
    (q : {q : ℝ // 0 < q ∧ q < 1}) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (q : ℝ) ^ (Nat.choose k 2) * x ^ k /
    (Nat.factorial k : ℝ)

end

end MathlibPlus.Analysis.Claim9538
