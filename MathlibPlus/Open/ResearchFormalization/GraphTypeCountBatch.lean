import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A finite simple graph on `Fin n` as a finite set of two-element vertex sets. -/
abbrev FiniteGraph (n : ℕ) := Finset (Finset (Fin n))

def validGraph {n : ℕ} (G : FiniteGraph n) : Prop :=
  ∀ e ∈ G, e.card = 2

def graphAdjacent {n : ℕ} (G : FiniteGraph n) (u v : Fin n) : Prop :=
  ∃ e : Finset (Fin n), e ∈ G ∧ u ∈ e ∧ v ∈ e

def graphConnected {n : ℕ} (G : FiniteGraph n) : Prop :=
  ∀ u v : Fin n, Relation.ReflTransGen (fun x y => graphAdjacent G x y) u v

def graphIsTree {n : ℕ} (G : FiniteGraph n) : Prop :=
  validGraph G ∧ graphConnected G ∧ G.card = n - 1

def graphIsomorphic {n : ℕ} (G H : FiniteGraph n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    ∀ u v : Fin n, graphAdjacent G u v ↔ graphAdjacent H (σ u) (σ v)

def typeSpecificSpanningTreeCount {n : ℕ}
    (G T : FiniteGraph n) : ℕ :=
  Fintype.card {H : FiniteGraph n // H ⊆ G ∧ graphIsTree H ∧ graphIsomorphic H T}

def totalSpanningTreeCount {n : ℕ} (G : FiniteGraph n) : ℕ :=
  Fintype.card {H : FiniteGraph n // H ⊆ G ∧ graphIsTree H}

/-- Claim 16139. -/
def TypeSpecificSpanningTreeCount : Prop :=
  ∀ (n : ℕ) (G T : FiniteGraph n),
    graphIsTree T →
      typeSpecificSpanningTreeCount G T =
        Fintype.card
          {H : FiniteGraph n // H ⊆ G ∧ graphIsTree H ∧ graphIsomorphic H T} ∧
      (∀ T' : FiniteGraph n,
        graphIsTree T' → graphIsomorphic T T' →
          typeSpecificSpanningTreeCount G T' = typeSpecificSpanningTreeCount G T)

end

end MathlibPlus.Open.ResearchFormalization
