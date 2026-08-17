import MathlibPlus.Open.ResearchFormalization.R0612Claim23310

namespace MathlibPlus.Open.ResearchFormalization.R0612Claim23311

open MathlibPlus.Open.ResearchFormalization.R0612Claim23310
noncomputable section

private abbrev FallingDeckRowIndex (n : ℕ) :=
  {S : Multiset R0612Claim23310.GraphClass // S.card ≤ 3}

private def initialPrivateFeatureRow {n : ℕ}
    (T : SimpleGraph (Fin n))
    (S : Multiset R0612Claim23310.GraphClass) : Prop :=
  S.card = 3 ∧
    cardSubmultisetOfDeck S T ∧
      0 < fallingCardRow S T ∧
        ∀ G : SimpleGraph (Fin n),
          graphColumnNonisomorphic T G → fallingCardRow S G = 0

/-- A degree-three falling deck row is a private pivot for every tree column;
the row index is the complete degree-at-most-three falling row carrier. -/
def treeColumnsInitialPrivatePivots_claim23311 : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    ∀ T : SimpleGraph (Fin n), T.IsTree →
      ∃ S : Multiset R0612Claim23310.GraphClass,
        S.card ≤ 3 ∧ initialPrivateFeatureRow T S

end

end MathlibPlus.Open.ResearchFormalization.R0612Claim23311
