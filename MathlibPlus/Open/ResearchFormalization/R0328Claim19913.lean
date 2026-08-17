import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0328Claim19913

noncomputable section

/-- An edge on the fixed vertex set `[n]`, represented by its two-element
endpoint set. -/
def Edge (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

abbrev Graph (n : ℕ) := Finset (Edge n)
abbrev GraphAlgebra (n : ℕ) := Graph n →₀ ℂ
abbrev RankGraph (n r : ℕ) := {G : Graph n // G.card = r}
abbrev RankGraphAlgebra (n r : ℕ) := RankGraph n r →₀ ℂ

def graphMonomial {n : ℕ} (G : Graph n) : GraphAlgebra n :=
  letI : DecidableEq (Edge n) := Classical.decEq _
  Finsupp.single G 1

/-- The edge-deletion operator on the fixed-vertex graph algebra. -/
def edgeDeleteBasis {n : ℕ} (G : Graph n) : GraphAlgebra n :=
  letI : DecidableEq (Edge n) := Classical.decEq _
  G.sum (fun e => graphMonomial (G.erase e))

def edgeDeleteOperator (n : ℕ) : GraphAlgebra n →ₗ[ℂ] GraphAlgebra n :=
  (Finsupp.lsum ℂ)
    (fun G => LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
      (edgeDeleteBasis G))

/-- The canonical inclusion of the r-edge graph algebra into the fixed-vertex
graph algebra. -/
def rankEmbedOperator (n r : ℕ) : RankGraphAlgebra n r →ₗ[ℂ] GraphAlgebra n :=
  (Finsupp.lsum ℂ)
    (fun G => LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
      (graphMonomial G.1))

def rankDeleteBasis {n r : ℕ} (G : RankGraph n r) :
    RankGraphAlgebra n (r - 1) :=
  letI : DecidableEq (Edge n) := Classical.decEq _
  G.1.attach.sum (fun e =>
    Finsupp.single
      ⟨G.1.erase e.1,
        (Finset.card_erase_of_mem e.2).trans
          (congrArg (fun k : ℕ => k - 1) G.2)⟩
      1)

def rankDeleteOperator (n r : ℕ) :
    RankGraphAlgebra n r →ₗ[ℂ] RankGraphAlgebra n (r - 1) :=
  (Finsupp.lsum ℂ)
    (fun G => LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
      (rankDeleteBasis G))

/-- The homogeneous r-edge subspace in the fixed-vertex graph algebra. -/
def rankSpace (n r : ℕ) : Submodule ℂ (GraphAlgebra n) :=
  Submodule.span ℂ {x | ∃ G : Graph n, G.card = r ∧ x = graphMonomial G}

/-- The primitive subspace in edge-rank r, before identifying it with the
kernel on the rank-indexed graph algebra. -/
def primitiveRankSpace (n r : ℕ) : Submodule ℂ (GraphAlgebra n) :=
  rankSpace n r ⊓ LinearMap.ker (edgeDeleteOperator n)

/-- Claim 19913: for every edge-rank, including r = 0, the primitive space is
exactly the image of the kernel of the rank-lowering deletion map. -/
def claim19913 : Prop :=
  ∀ (n r : ℕ),
    primitiveRankSpace n r =
      Submodule.map (rankEmbedOperator n r)
        (LinearMap.ker (rankDeleteOperator n r))

end
end MathlibPlus.Open.ResearchFormalization.R0328Claim19913
