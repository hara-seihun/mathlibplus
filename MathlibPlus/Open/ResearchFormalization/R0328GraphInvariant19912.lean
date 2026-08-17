import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0328

def claim19912_graphInvariantSl2Submodule : Prop :=
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
    let permuteGraph : Equiv.Perm (Fin n) → Graph → Graph :=
      fun σ G => SimpleGraph.map (σ : Fin n → Fin n) G
    ∃ (E F H : Space →ₗ[ℂ] Space)
      (P : Equiv.Perm (Fin n) → Space →ₗ[ℂ] Space),
      (∀ G : Graph,
        E (basis G) =
          Finset.sum (allEdges.filter (fun e => e ∉ G.edgeSet))
            (fun e => basis (addEdge G e))) ∧
      (∀ G : Graph,
        F (basis G) =
          Finset.sum (allEdges.filter (fun e => e ∈ G.edgeSet))
            (fun e => basis (deleteEdge G e))) ∧
      (∀ G : Graph,
        H (basis G) = (G.edgeSet.ncard : ℂ) • basis G) ∧
      (∀ (σ : Equiv.Perm (Fin n)) (G : Graph),
        P σ (basis G) = basis (permuteGraph σ G)) ∧
      P (1 : Equiv.Perm (Fin n)) = (LinearMap.id : Space →ₗ[ℂ] Space) ∧
      (∀ (σ τ : Equiv.Perm (Fin n)),
        P (σ * τ) = (P σ).comp (P τ)) ∧
      (∀ (σ : Equiv.Perm (Fin n)) (G : Graph),
        (permuteGraph σ G).edgeSet.ncard = G.edgeSet.ncard) ∧
      ∃ invariant : Submodule ℂ Space,
        (∀ x : Space,
          x ∈ invariant ↔
            ∀ σ : Equiv.Perm (Fin n), P σ x = x) ∧
        (∀ (x : Space), x ∈ invariant →
          E x ∈ invariant ∧ F x ∈ invariant ∧ H x ∈ invariant)

end MathlibPlus.Open.ResearchFormalization.R0328
