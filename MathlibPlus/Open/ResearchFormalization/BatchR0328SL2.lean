import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0328

/-- Claim 19907: the exact fixed-vertex Boolean edge cube carries the
edge-addition/deletion operators and the standard grading with the stated
`sl₂` commutator convention. -/
def claim19907_booleanLatticeSL2Action : Prop :=
  ∀ n : ℕ,
    let Graph := SimpleGraph (Fin n)
    let Space := Graph →₀ ℂ
    let basis : Module.Basis Graph ℂ Space := Finsupp.basisSingleOne
    let allEdges : Finset (Sym2 (Fin n)) :=
      Finset.univ.filter (fun e => e ∈ (⊤ : Graph).edgeSet)
    letI : ∀ G : Graph, DecidablePred (fun e => e ∈ G.edgeSet) :=
      fun G e => Classical.propDecidable _
    let addEdge : Graph → Sym2 (Fin n) → Graph :=
      fun G e => SimpleGraph.fromEdgeSet (G.edgeSet ∪ {e})
    let deleteEdge : Graph → Sym2 (Fin n) → Graph :=
      fun G e => SimpleGraph.fromEdgeSet (G.edgeSet \ {e})
    ∃ (E F H : Space →ₗ[ℂ] Space),
      (∀ G : Graph,
        E (basis G) =
          Finset.sum (allEdges.filter (fun e => e ∉ G.edgeSet))
            (fun e => basis (addEdge G e))) ∧
      (∀ G : Graph,
        F (basis G) =
          Finset.sum (allEdges.filter (fun e => e ∈ G.edgeSet))
            (fun e => basis (deleteEdge G e))) ∧
      (∀ G : Graph,
        H (basis G) =
          ((2 : ℂ) * (G.edgeSet.ncard : ℂ) -
            (n.choose 2 : ℂ)) • basis G) ∧
      E.comp F - F.comp E = H ∧
      H.comp E - E.comp H = (2 : ℂ) • E ∧
      H.comp F - F.comp H = (-2 : ℂ) • F

end MathlibPlus.Open.ResearchFormalization.BatchR0328
