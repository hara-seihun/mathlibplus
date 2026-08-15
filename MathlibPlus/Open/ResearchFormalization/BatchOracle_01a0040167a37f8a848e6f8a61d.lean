import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

/-! Fixed-level oracle-area defect identity and rigidity. -/
def claim60027 : Prop :=
  ∀ {ι : Type*} (Q : Finset ι) (a c : ι → ℝ),
    (∀ i ∈ Q, a i ≤ c i ∧ c i ≤ 1) →
      let k : ℝ := Q.card
      let A : ℝ := ∑ i ∈ Q, a i
      A ≤ k ∧
        k - A = ∑ i ∈ Q, (1 - a i) ∧
        (A = k ↔ ∀ i ∈ Q, a i = 1 ∧ c i = 1) ∧
        ∃ a' c' : ι → ℝ,
          (∀ i ∈ Q, a' i ≤ c' i ∧ c' i ≤ 1) ∧
          (∀ i ∈ Q, a' i = 1 ∧ c' i = 1) ∧
          (∑ i ∈ Q, a' i) = k

end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
