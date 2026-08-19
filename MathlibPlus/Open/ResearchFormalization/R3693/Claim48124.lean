import MathlibPlus.Combinatorics.StrongOrdering

namespace MathlibPlus.Open.ResearchFormalization.R3693.Claim48124

open MathlibPlus.Combinatorics

/-- The endpoint cuts in an insertion-maximal strong ordering force both
translated copies of the unused set into the prefix-sum set. -/
def claim48124 : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (A : Finset G) (B : List G),
    letI : DecidableEq G := Classical.decEq G
    0 ∉ A →
      B.Nodup →
        (∀ x ∈ B, x ∈ A) →
          strongOrdering B →
            (∀ u ∈ A, u ∉ B →
              ∀ k : ℕ, k ≤ B.length →
                ¬ strongOrdering (B.take k ++ [u] ++ B.drop k)) →
              let U : Finset G := A \ B.toFinset
              let r : ℕ := B.length
              let X : Finset G :=
                (B.scanl (fun s a => s + a) 0).toFinset
              let T : G := B.sum
              let minusU : Finset G := U.image (fun u : G => -u)
              let totalPlusU : Finset G := U.image (fun u : G => T + u)
              X.card = r + 1 ∧
                (∀ u ∈ U, -u ∈ X ∧ T + u ∈ X) ∧
                minusU ⊆ X ∧ totalPlusU ⊆ X

end MathlibPlus.Open.ResearchFormalization.R3693.Claim48124
