import MathlibPlus.Open.ResearchFormalizationBatch019ffee247417e52a3777372619c2f85
import MathlibPlus.Combinatorics.Claim44788

namespace MathlibPlus.Open.ResearchFormalization.R2953

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Claim 44790: pairwise-coherent local card isomorphisms induce one global
finite graph isomorphism. -/
def coherentLocalCardsGiveGlobalIsomorphism_claim44790 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) (π : V → Equiv.Perm V),
    3 ≤ Fintype.card V →
    (∀ i : V,
      MathlibPlus.Open.ResearchFormalizationBatch.inducesDeletedCardIso
        A B i (π i)) →
    MathlibPlus.Combinatorics.Claim44788.pairwiseCoherent
      (fun i x => π i x) →
    ∃ σ : Equiv.Perm V,
      (∀ x : V, ∀ i : V, i ≠ x → σ x = π i x) ∧
      (∀ x y : V, A.Adj x y ↔ B.Adj (σ x) (σ y))

end

end MathlibPlus.Open.ResearchFormalization.R2953
