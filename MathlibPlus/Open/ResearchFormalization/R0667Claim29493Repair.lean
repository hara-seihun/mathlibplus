import MathlibPlus.Open.ResearchFormalizationBatch.R0667

namespace MathlibPlus.Open.ResearchFormalization.R0667Claim29493Repair

open MathlibPlus.Open.ResearchFormalizationBatch.R0667

noncomputable section

/-- Exactly one of three propositions holds. -/
def exactlyOne3 (p q r : Prop) : Prop :=
  (p ∧ ¬q ∧ ¬r) ∨
    (¬p ∧ q ∧ ¬r) ∨
    (¬p ∧ ¬q ∧ r)

/-- Claim 29493: the three nontransverse deletion-origin channels form an
exclusive and exhaustive trichotomy. -/
def exhaustiveNontransverseTrichotomy_claim29493 : Prop :=
  ∀ {B P K : Type*} [Fintype B] [DecidableEq B]
    [Fintype P] [DecidableEq P] [Fintype K] [DecidableEq K]
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B),
    let H := apexMaskExtension F S
    graphIsomorphic F (deleteGraph H ({none} : Finset (Option B))) →
      ∀ (u v w : Option B), v ≠ w →
        graphIsomorphic Pgraph (deleteGraph H ({u} : Finset (Option B))) →
        graphIsomorphic Kgraph
          (deleteGraph H ({v, w} : Finset (Option B))) →
        ¬ (u ≠ none ∧ v ≠ none ∧ w ≠ none ∧
          u ≠ v ∧ u ≠ w ∧ v ≠ w) →
        exactlyOne3
          (u = none ∧ graphIsomorphic Pgraph F)
          (u ≠ none ∧ (v = none ∨ w = none) ∧
            ∃ b : B, graphIsomorphic Kgraph (deleteGraph F {b}))
          (u ≠ none ∧ v ≠ none ∧ w ≠ none ∧ (u = v ∨ u = w) ∧
            ∃ p : P, graphIsomorphic Kgraph (deleteGraph Pgraph {p}))

end

end MathlibPlus.Open.ResearchFormalization.R0667Claim29493Repair
