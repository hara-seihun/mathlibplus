import Mathlib

namespace MathlibPlus.Open.Research.CayleyCI

open Classical

noncomputable section

abbrev F3 := ZMod 3
abbrev CayleySpace := Fin 3 → F3

def identityFree (S : Set CayleySpace) : Prop :=
  (0 : CayleySpace) ∉ S

def inverseClosed (S : Set CayleySpace) : Prop :=
  ∀ ⦃x : CayleySpace⦄, x ∈ S → -x ∈ S

/-- The adjacency matrix of the ordinary undirected additive Cayley graph. -/
def cayleyAdjacency (S : Set CayleySpace) : Matrix CayleySpace CayleySpace ℂ :=
  fun x z => if z - x ∈ S then 1 else 0

def sameAdjacencySpectrum (S T : Set CayleySpace) : Prop :=
  Matrix.charpoly (cayleyAdjacency S) = Matrix.charpoly (cayleyAdjacency T)

/-- Claim 59950: `F₃^3` is a CI-group for ordinary undirected Cayley graphs. -/
def claim_59950_cayleyCI : Prop :=
  ∀ (S T : Set CayleySpace),
    identityFree S →
    inverseClosed S →
    identityFree T →
    inverseClosed T →
    sameAdjacencySpectrum S T →
    ∃ A : CayleySpace ≃ₗ[F3] CayleySpace, A '' S = T

end

end MathlibPlus.Open.Research.CayleyCI
