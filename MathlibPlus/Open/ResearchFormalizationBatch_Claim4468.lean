import MathlibPlus.Open.ResearchFormalizationBatch_01a001ac_7d55_7d4a_8f44_f4a292b299c9

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 4468: finite square and higher-channel energies are nonnegative at
nonnegative real inputs, for every finite support and cutoff. -/
def claim4468_finite_energies_nonnegative : Prop :=
  ∀ (support : Finset ℕ) (sequence : ℕ → ℝ) (N : ℕ) (x : ℝ),
    0 ≤ x →
      0 ≤ finiteSquareEnergy support sequence N x ∧
        0 ≤ ∑ r ∈ Finset.range N,
          x ^ (r + 1) *
              (finiteChannel support sequence (r + 1) x) ^ 2 /
            ((r + 1).factorial : ℝ)

end MathlibPlus.Open.ResearchFormalizationBatch
