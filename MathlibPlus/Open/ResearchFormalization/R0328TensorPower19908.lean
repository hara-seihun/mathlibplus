import Mathlib

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.ResearchFormalization.R0328

def claim19908_tensorPowerModel : Prop :=
  ∀ n : ℕ,
    let Graph := SimpleGraph (Fin n)
    let Space := Graph →₀ ℂ
    let basis : Module.Basis Graph ℂ Space := Finsupp.basisSingleOne
    let Edge := {e : Sym2 (Fin n) // e ∈ (⊤ : Graph).edgeSet}
    let Factor := Fin 2 → ℂ
    let Tensor := PiTensorProduct ℂ (fun _ : Edge => Factor)
    let allEdges : Finset Edge := Finset.univ
    letI : ∀ G : Graph, DecidablePred (fun e => e ∈ G.edgeSet) :=
      fun G e => Classical.propDecidable _
    let addEdge : Graph → Sym2 (Fin n) → Graph :=
      fun G e => SimpleGraph.fromEdgeSet (G.edgeSet ∪ {e})
    let deleteEdge : Graph → Sym2 (Fin n) → Graph :=
      fun G e => SimpleGraph.fromEdgeSet (G.edgeSet \ {e})
    let stdBasis : Module.Basis (Fin 2) ℂ Factor := Pi.basisFun ℂ (Fin 2)
    let zeroVector : Factor := Pi.single 0 1
    let oneVector : Factor := Pi.single 1 1
    let factorE : Factor →ₗ[ℂ] Factor :=
      stdBasis.constr ℂ (fun i => if i = 0 then oneVector else 0)
    let factorF : Factor →ₗ[ℂ] Factor :=
      stdBasis.constr ℂ (fun i => if i = 1 then zeroVector else 0)
    let factorH : Factor →ₗ[ℂ] Factor :=
      stdBasis.constr ℂ
        (fun i => if i = 0 then (-1 : ℂ) • zeroVector else oneVector)
    let factorRank : Factor →ₗ[ℂ] Factor :=
      stdBasis.constr ℂ (fun i => if i = 1 then oneVector else 0)
    let tensorE : Tensor →ₗ[ℂ] Tensor :=
      ∑ i : Edge,
        PiTensorProduct.map (fun j =>
          if i = j then factorE else (LinearMap.id : Factor →ₗ[ℂ] Factor))
    let tensorF : Tensor →ₗ[ℂ] Tensor :=
      ∑ i : Edge,
        PiTensorProduct.map (fun j =>
          if i = j then factorF else (LinearMap.id : Factor →ₗ[ℂ] Factor))
    let tensorH : Tensor →ₗ[ℂ] Tensor :=
      ∑ i : Edge,
        PiTensorProduct.map (fun j =>
          if i = j then factorH else (LinearMap.id : Factor →ₗ[ℂ] Factor))
    let tensorRank : Tensor →ₗ[ℂ] Tensor :=
      ∑ i : Edge,
        PiTensorProduct.map (fun j =>
          if i = j then factorRank else (LinearMap.id : Factor →ₗ[ℂ] Factor))
    (Fintype.card Edge = n.choose 2) ∧
      Module.finrank ℂ Factor = 2 ∧
      ∃ (E F H rank : Space →ₗ[ℂ] Space)
        (equiv : Space ≃ₗ[ℂ] Tensor),
        (∀ G : Graph,
          E (basis G) =
            Finset.sum (allEdges.filter
              (fun (e : Edge) => (e : Sym2 (Fin n)) ∉ G.edgeSet))
              (fun e => basis (addEdge G e))) ∧
        (∀ G : Graph,
          F (basis G) =
            Finset.sum (allEdges.filter
              (fun (e : Edge) => (e : Sym2 (Fin n)) ∈ G.edgeSet))
              (fun e => basis (deleteEdge G e))) ∧
        (∀ G : Graph,
          H (basis G) =
            ((2 : ℂ) * (G.edgeSet.ncard : ℂ) - (Fintype.card Edge : ℂ)) •
              basis G) ∧
        (∀ x : Space, equiv (E x) = tensorE (equiv x)) ∧
        (∀ x : Space, equiv (F x) = tensorF (equiv x)) ∧
        (∀ x : Space, equiv (H x) = tensorH (equiv x)) ∧
        (∀ G : Graph,
          rank (basis G) = (G.edgeSet.ncard : ℂ) • basis G) ∧
        (∀ x : Space, equiv (rank x) = tensorRank (equiv x))

end MathlibPlus.Open.ResearchFormalization.R0328
