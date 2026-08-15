import Mathlib

namespace MathlibPlus.Open.Analysis.Claim9547

noncomputable def truncatedQExponential (q : ℝ) (n : ℕ) : Polynomial ℂ :=
  (Finset.range (n + 1)).sum fun k =>
    Polynomial.C (((q ^ (Nat.choose k 2) / (Nat.factorial k : ℝ)) : ℝ) : ℂ) *
      (Polynomial.X : Polynomial ℂ) ^ k

noncomputable def thetaEdgeGamma (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) + 1 / Real.sqrt n

noncomputable def thetaEdgeParameter (n : ℕ) : ℝ :=
  Real.exp (-2 * thetaEdgeGamma n / n)

def allRootsReal (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, p.IsRoot z → z.im = 0

def thetaEdgeSequenceAllRealRooted : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    allRootsReal (truncatedQExponential (thetaEdgeParameter n) n)

def statement : Prop :=
  ¬ thetaEdgeSequenceAllRealRooted ∧
    ¬ allRootsReal (truncatedQExponential (thetaEdgeParameter 4) 4)

end MathlibPlus.Open.Analysis.Claim9547
