import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0328

def claim19906_edgeOperators : Prop :=
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
    ∃ (E F : Space →ₗ[ℂ] Space),
      (∀ G : Graph,
        E (basis G) =
          Finset.sum (allEdges.filter (fun e => e ∉ G.edgeSet))
            (fun e => basis (addEdge G e))) ∧
      (∀ G : Graph,
        F (basis G) =
          Finset.sum (allEdges.filter (fun e => e ∈ G.edgeSet))
            (fun e => basis (deleteEdge G e))) ∧
      (∀ (G : Graph) (e : Sym2 (Fin n)),
        e ∈ allEdges → e ∉ G.edgeSet →
          (addEdge G e).edgeSet.ncard = G.edgeSet.ncard + 1) ∧
      (∀ (G : Graph) (e : Sym2 (Fin n)),
        e ∈ G.edgeSet →
          (deleteEdge G e).edgeSet.ncard = G.edgeSet.ncard - 1)

end MathlibPlus.Open.ResearchFormalization.R0328
