import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace MathlibPlus.Combinatorics

/-- Claim 52355: the neutral-packing and nonnegative-base-slack inequalities
imply the stated lower bound for the mismatch-cover objective.  The cover
semantics and the source-specific slack identity are represented by the three
explicit hypotheses. -/
theorem neutralPackingObjective_claim52355
    {ι : Type*} [Fintype ι]
    (y mb sₗ sₚ : ι → ℝ) (t : ℝ)
    (hpack : t ≤ ∑ k : ι, y k * mb k)
    (hbase : 0 ≤ ∑ k : ι, y k * sₚ k)
    (hobjective :
      t + (1 / 2 : ℝ) * (∑ k : ι, y k * sₚ k) ≤
        (1 / 2 : ℝ) * (∑ k : ι, y k * sₗ k)) :
    t ≤ ∑ k : ι, y k * mb k ∧
      t ≤ (1 / 2 : ℝ) * (∑ k : ι, y k * sₗ k) := by
  constructor
  · exact hpack
  · linarith

end MathlibPlus.Combinatorics
