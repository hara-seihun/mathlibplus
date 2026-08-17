import MathlibPlus.Open.ResearchFormalization.R0612Claim23310

namespace MathlibPlus.Open.ResearchFormalization.R0612Claim23308

open MathlibPlus.Open.ResearchFormalization.R0612Claim23310

noncomputable section

/-- Claim 23308: every tree on at least five vertices has a three-card
vertex-deleted submultiset private from every nonisomorphic graph column of
the same order. -/
def claim23308 : Prop :=
  ∀ (n : ℕ),
    5 ≤ n →
      ∀ T : SimpleGraph (Fin n),
        T.IsTree →
          ∃ S : Multiset GraphClass,
            S.card = 3 ∧
              cardSubmultisetOfDeck S T ∧
                ∀ G : SimpleGraph (Fin n),
                  graphColumnNonisomorphic T G →
                    ¬ cardSubmultisetOfDeck S G

end

end MathlibPlus.Open.ResearchFormalization.R0612Claim23308
