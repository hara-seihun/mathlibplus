import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 53887: under the retained strict-shift and one-call slot
hypotheses, root-shift aggregation exceeds twice the whole-band lag. -/
def aggregateUniformGridLowerBound_claim53887 : Prop :=
  ∀ (α W : ℝ) (M slotsPerCall : ℕ),
    0 < W →
      0 < α →
        (1 / 2 : ℝ) < (M : ℝ) * α →
          4 * Nat.ceil (α * W) ≤ slotsPerCall →
            ((4 * (M : ℝ) *
                (Nat.ceil (α * W) : ℝ) ≤
                ((M * slotsPerCall : ℕ) : ℝ)) ∧
              (4 * (M : ℝ) * (α * W) ≤
                4 * (M : ℝ) * (Nat.ceil (α * W) : ℝ)) ∧
              (2 * W < 4 * (M : ℝ) * (α * W)))

end MathlibPlus.Open.Analysis
