import MathlibPlus.Open.ResearchFormalization.R2662Contraction

namespace MathlibPlus.Open.ResearchFormalization.R2662

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Combinatorics.Claim42226

/-- Claim 42227: under the exact five-type profile, the fiber weights are
`2, 3, 3, 3, 8`, the family and outside-support cardinalities are
`2 * k + 17` and `k + 4`, and the principal-filter deficit at `M` is `9`.
-/
def exactProfileCardinalitiesAndDeficit_claim42227 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (k : ℕ) (m : Fin 3 → α),
    deficitNineTraceProfile F M k m →
    let Sigma := outsideSupports F M
    (∀ S : Finset α,
      supportCarriesTrace F M S (neutralTrace M) →
        Set.ncard (outsideSupportTraceFiber F M S) = 2) ∧
      (∀ i : Fin 3, ∀ S : Finset α,
        supportCarriesTrace F M S (singletonTrace M (m i)) →
          Set.ncard (outsideSupportTraceFiber F M S) = 3) ∧
      (∀ C : Finset α,
        supportCarriesTrace F M C (fullTrace M) →
          Set.ncard (outsideSupportTraceFiber F M C) = 8) ∧
      F.card = 2 * k + 17 ∧
      Set.ncard Sigma = k + 4 ∧
      (F.filter (fun A => M ⊆ A)).card = k + 4 ∧
      (∀ hM : M ∈ F,
        principalFilterDeficit F M hM = 9)

end

end MathlibPlus.Open.ResearchFormalization.R2662
