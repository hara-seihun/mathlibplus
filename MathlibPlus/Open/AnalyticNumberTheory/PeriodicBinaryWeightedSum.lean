import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- The exact periodic-binary weighted-sum assertion from claim 51694.
The sequence is indexed at zero; the displayed residue sum uses residues
`1, ..., p`, matching the packet's convention that the zero residue is `p`.
The final non-equality records the packet's `1/3` exclusion; its parity proof
is intentionally left in the registry node rather than replaced by a weaker
finite assertion. -/
def periodicBinaryWeightedSum_claim51694 : Prop :=
  ∀ p : ℕ, 0 < p →
    ∀ e : ℕ → ℕ,
      (∀ k : ℕ, e k ≤ 1) →
      (∀ k : ℕ, e (k + p) = e k) →
      let Q : ℝ := (2 : ℝ) ^ p
      let value : ℝ :=
        ∑' k : ℕ, (e k : ℝ) * (k : ℝ) / (2 : ℝ) ^ k
      let residue : ℝ :=
        ∑ r ∈ Finset.Icc 1 p,
          (e r : ℝ) * (2 : ℝ) ^ (p - r) *
            ((r : ℝ) * (Q - 1) + (p : ℝ)) / (Q - 1) ^ 2
      value = residue ∧ value ≠ (1 : ℝ) / 3

end MathlibPlus.Open.AnalyticNumberTheory
