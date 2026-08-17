import MathlibPlus.Open.AdmittedBatch.Combinatorics
import MathlibPlus.Open.Combinatorics.R0392Collision

namespace MathlibPlus.Open.Combinatorics.R0392

open MathlibPlus.Open.AdmittedBatch.MarginClaims

/-- Claim 20852: the exact proper-margin profile cannot distinguish the
explicit uniform sunflower/non-sunflower collision. -/
def properMarginsCannotDetectThreeSunflowers_claim20852 : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ {V : Type*} [DecidableEq V]
      (U C : Finset V) (a b c d : V),
      C ⊆ U →
      U.card = n + 2 →
      C.card = n - 2 →
      a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ d ∈ U ∧
        a ∉ C ∧ b ∉ C ∧ c ∉ C ∧ d ∉ C ∧
          a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d →
      let first : Fin 3 → Finset V :=
        ![C ∪ {a, b}, C ∪ {a, c}, C ∪ {a, d}]
      let second : Fin 3 → Finset V :=
        ![C ∪ {a, b}, C ∪ {a, c}, C ∪ {b, c}]
      Function.Injective first ∧
        Function.Injective second ∧
        first ≠ second ∧
        (∀ i : Fin 3, (first i).card = n ∧ (second i).card = n) ∧
        sunflowerWithCore first (C ∪ {a}) ∧
        ¬ isSunflower second ∧
        (∀ (β : Type*)
          (statistic : (ℕ × (properSubset3 → ℕ)) → β),
          statistic (properMarginProfile U first) =
            statistic (properMarginProfile U second))

end MathlibPlus.Open.Combinatorics.R0392
