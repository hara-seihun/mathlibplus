import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
import MathlibPlus.Open.ResearchFormalization.GraphDeckBatch
import MathlibPlus.Open.GraphTheory.GraphTypeCountsBatch

namespace MathlibPlus.GraphTheory.Claim31492

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
open MathlibPlus.Open.GraphFourier.TypeCountsBatch

private def edge01 : CompleteEdge 3 :=
  ⟨{(0 : Fin 3), (1 : Fin 3)}, by decide⟩

private def edge02 : CompleteEdge 3 :=
  ⟨{(0 : Fin 3), (2 : Fin 3)}, by decide⟩

private def edge12 : CompleteEdge 3 :=
  ⟨{(1 : Fin 3), (2 : Fin 3)}, by decide⟩

private def pathThree : LabeledGraph 3 :=
  {edge01, edge12}

private def triangleThree : LabeledGraph 3 :=
  {edge01, edge02, edge12}

private def graphFrom (G : LabeledGraph 3) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun u v =>
    ∃ e : CompleteEdge 3, e ∈ G ∧ u ∈ e.1 ∧ v ∈ e.1)

private def deckDetermined (f : LabeledGraph 3 → ℚ) : Prop :=
  ∀ G H : LabeledGraph 3,
    vertexDeckEqual (graphFrom G) (graphFrom H) → f G = f H

private def spanningCoordinate : Fin 2 → (LabeledGraph 3 → ℚ) :=
  ![shapeCharacterQ pathThree, shapeCharacterQ triangleThree]

private def spanningDeckSubspace :
    Submodule ℚ (LabeledGraph 3 → ℚ) :=
  Submodule.span ℚ (Set.range spanningCoordinate)

/--
At order three the path and triangle spanning coordinates are separated by
vertex-deleted decks, and their exact two-coordinate span is deck-determined
and two-dimensional.
-/
def orderThreeSpanningDeckSubspace_claim31492 : Prop :=
  spanningTypeCount 3 = 2 ∧
    ¬ vertexDeckEqual (graphFrom pathThree) (graphFrom triangleThree) ∧
    (∀ i : Fin 2, deckDetermined (spanningCoordinate i)) ∧
    (∀ f : LabeledGraph 3 → ℚ,
      f ∈ spanningDeckSubspace → deckDetermined f) ∧
    Module.finrank ℚ spanningDeckSubspace = 2

end MathlibPlus.GraphTheory.Claim31492
