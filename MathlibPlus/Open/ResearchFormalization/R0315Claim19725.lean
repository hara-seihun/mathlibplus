import MathlibPlus.Open.ResearchFormalization.R0315ExtensionClaims

open MathlibPlus.Open.ResearchFormalization.R0315ExtensionClaims

namespace MathlibPlus.Open.ResearchFormalization.R0315Claim19725

/-- Claim 19725: the two extension tops are absent from the finite family, their
union belongs to the family, and adjoining either top gives either a family
member or that same absent top, with the non-containment implication retaining
family membership. -/
def claim19725 : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (tight : Fin 3 → X)
    (topTight : Fin 2 → X) (tops : Fin 2 → Finset X),
    exactExtensionCoreContext G T tight topTight tops →
      (∀ i : Fin 2, tops i ∉ G) ∧
        tops 0 ∪ tops 1 ∈ G ∧
        (∀ i : Fin 2, ∀ A ∈ G,
          A ∪ tops i ∈ (G ∪ {tops i}) ∧
            (¬ (A ⊆ tops i) → A ∪ tops i ∈ G))

end MathlibPlus.Open.ResearchFormalization.R0315Claim19725
