import MathlibPlus.Combinatorics.StrongOrdering

namespace MathlibPlus.Open.Combinatorics.Q0130

open MathlibPlus.Combinatorics

/-- Claim 16776: an insertion-maximal strong path uses at least the natural
ceiling of half of the label set. -/
def insertionMaximalStrongPathHalfScale_claim16776 : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (A : Finset G) (B : List G),
    0 ∉ A →
    B.Nodup →
    (∀ x ∈ B, x ∈ A) →
    strongOrdering B →
    (∀ u ∈ A, u ∉ B →
      ∀ k : ℕ, k ≤ B.length →
        ¬ strongOrdering (B.take k ++ [u] ++ B.drop k)) →
    B.length ≥ (A.card + 1) / 2

end MathlibPlus.Open.Combinatorics.Q0130
