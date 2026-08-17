import Mathlib
import MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460

namespace MathlibPlus.Open.ResearchFormalization.BatchR0415Claim21146

/-- Claim 21146: the exact normalized size-seven union product is realized by
nonempty distinct finite union-closed factors of size eighteen, with empty
total intersections and empty-set exclusion. -/
def claim21146_productSizeSevenCounterexample : Prop :=
  ∃ (n : ℕ)
    (A B : Finset (Finset (Fin n))),
    A.Nonempty ∧
      B.Nonempty ∧
      (∅ : Finset (Fin n)) ∉ A ∧
      (∅ : Finset (Fin n)) ∉ B ∧
      MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.IsUnionClosedFamily A ∧
      MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.IsUnionClosedFamily B ∧
      MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.HasEmptyTotalIntersection A ∧
      MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.HasEmptyTotalIntersection B ∧
      (MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.joinFamily A B).card = 7 ∧
      A.card = 18 ∧
      B.card = 18

end MathlibPlus.Open.ResearchFormalization.BatchR0415Claim21146
