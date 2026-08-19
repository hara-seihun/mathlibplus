import MathlibPlus.Open.C0079NeighboringMinor

namespace MathlibPlus.Open.ResearchFormalization.BatchC0077

open scoped BigOperators
open MathlibPlus.Open.C0079

noncomputable section

/-- The unshifted principal pair-sum product. -/
def principalPairProductAt1156 (d : ℕ) (a : ℝ) : ℝ :=
  (Nat.factorial d : ℝ) *
    Finset.prod (Finset.range (d + 1)) (fun p =>
      Finset.prod (Finset.range (d + 1)) (fun q =>
        if p < q then 2 * a + (p : ℝ) + (q : ℝ) else 1))

/-- The same product in the half-shift variable `b`. -/
def shiftedPrincipalPairProduct1156 (d : ℕ) (b : ℝ) : ℝ :=
  (Nat.factorial d : ℝ) *
    Finset.prod (Finset.range (d + 1)) (fun p =>
      Finset.prod (Finset.range (d + 1)) (fun q =>
        if p < q then 2 * b + (p : ℝ) + (q : ℝ) + 1 else 1))

/-- Claim 1156: the principal flagged determinant is the exact pair-sum
product, and after `a = b + 1/2` it is exactly `P_d(b)`. -/
def principalFlaggedDeterminantProduct_claim1156 : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ a b : ℝ, a = b + 1 / 2 →
    let Hempty : ℝ := emptyMinor d a
    Hempty = principalPairProductAt1156 d a ∧
      Hempty = shiftedPrincipalPairProduct1156 d b

end

end MathlibPlus.Open.ResearchFormalization.BatchC0077
