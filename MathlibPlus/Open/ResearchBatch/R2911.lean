import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.R2911

abbrev C9 := ZMod 9

def inverseClosed (X : Set C9) : Prop := ∀ x, x ∈ X → -x ∈ X
def primitiveNinthRoot (z : ℂ) : Prop :=
  z^9 = 1 ∧ ∀ k : ℕ, 0 < k → k < 9 → z^k ≠ 1
def rootSum (z : ℂ) (X : Set C9) (j : ℕ) : ℂ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x : C9 => x ∈ X), z ^ (j * x.val)

def primitiveNinthRootCharacterization_claim47435 : Prop :=
  ∀ (z : ℂ), primitiveNinthRoot z →
    ∀ X : Set C9, inverseClosed X →
      (rootSum z X 1 = rootSum z X 3 ↔
        X = ∅ ∨ X = ({0} : Set C9) ∨
        X = (Set.univ \ ({0} : Set C9)) ∨ X = Set.univ)

end MathlibPlus.Open.ResearchBatch.R2911
