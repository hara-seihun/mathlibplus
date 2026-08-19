import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
import MathlibPlus.Open.Combinatorics.FiniteGraphDeckClaims

namespace MathlibPlus.Open.ResearchFormalization.R2781SpanningDeck

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
open MathlibPlus.Open.Combinatorics.FiniteGraphDeck

attribute [local instance] Classical.propDecidable Classical.decEq

private def edgeIn {n : ℕ}
    (A : LabeledGraph n) (v w : Fin n) : Prop :=
  v ≠ w ∧
    ∃ e : CompleteEdge n,
      e ∈ A ∧ (e : Finset (Fin n)) = {v, w}

private def graphOfEdges {n : ℕ} (A : LabeledGraph n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (edgeIn A)

private def spanningShape {n : ℕ} (A : LabeledGraph n) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, edgeIn A v w

private def connectedSpanningShape {n : ℕ} (A : LabeledGraph n) : Prop :=
  spanningShape A ∧ (graphOfEdges A).Connected

private def deckDeterminedShape {n : ℕ} (A : LabeledGraph n) : Prop :=
  ∀ G H : LabeledGraph n,
    vertexDeck (⟨n, graphOfEdges G⟩) =
        vertexDeck (⟨n, graphOfEdges H⟩) →
      shapeCharacter A G = shapeCharacter A H

private def spanningDeckSpan (n : ℕ) :
    Submodule ℚ (LabeledGraph n → ℚ) :=
  Submodule.span ℚ
    (Set.range
      (fun A : {A : LabeledGraph n // spanningShape A ∧ deckDeterminedShape A} =>
        fun G : LabeledGraph n => shapeCharacterQ A.1 G))

private def connectedDeckSpan (n : ℕ) :
    Submodule ℚ (LabeledGraph n → ℚ) :=
  Submodule.span ℚ
    (Set.range
      (fun A : {A : LabeledGraph n // connectedSpanningShape A ∧
          deckDeterminedShape A} =>
        fun G : LabeledGraph n => shapeCharacterQ A.1 G))

private def spanningDeckDimension (n : ℕ) : ℕ :=
  Module.finrank ℚ (spanningDeckSpan n)

private def connectedDeckDimension (n : ℕ) : ℕ :=
  Module.finrank ℚ (connectedDeckSpan n)

/-- Claim 31495: every spanning shape character through orders three to
seven is determined by the multiset of vertex-deleted graph isomorphism
classes, with the exact spanning and connected-spanning dimensions. -/
def claim31495 : Prop :=
  (∀ n : ℕ, 3 ≤ n → n ≤ 7 →
    ∀ A : LabeledGraph n, spanningShape A → deckDeterminedShape A) ∧
  spanningDeckDimension 2 = 0 ∧
  spanningDeckDimension 3 = 2 ∧
  spanningDeckDimension 4 = 7 ∧
  spanningDeckDimension 5 = 23 ∧
  spanningDeckDimension 6 = 122 ∧
  spanningDeckDimension 7 = 888 ∧
  connectedDeckDimension 2 = 0 ∧
  connectedDeckDimension 3 = 2 ∧
  connectedDeckDimension 4 = 6 ∧
  connectedDeckDimension 5 = 21 ∧
  connectedDeckDimension 6 = 112 ∧
  connectedDeckDimension 7 = 853

end

end MathlibPlus.Open.ResearchFormalization.R2781SpanningDeck
