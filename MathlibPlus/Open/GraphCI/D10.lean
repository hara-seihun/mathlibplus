import Mathlib

namespace MathlibPlus.Open.GraphCI

/-- A connection set for an undirected Cayley graph is inverse-closed and omits
    the identity, so that the graph has no loops. -/
def isUndirectedConnectionSet {G : Type*} [Group G] (S : Set G) : Prop :=
  1 ∉ S ∧ ∀ g, g ∈ S ↔ g⁻¹ ∈ S

/-- The simple undirected Cayley graph associated with a connection set. -/
def undirectedCayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun g h => g⁻¹ * h ∈ S)

/-- Two connection sets are equivalent when a group automorphism carries one to
    the other. -/
def relatedByGroupAutomorphism {G : Type*} [Group G] (S T : Set G) : Prop :=
  ∃ e : G ≃* G, e '' S = T

/-- The undirected CI property for a finite group. -/
def isFiniteUndirectedCIGroup (G : Type*) [Group G] [Fintype G] : Prop :=
  ∀ S T : Set G,
    isUndirectedConnectionSet S →
    isUndirectedConnectionSet T →
    Nonempty (undirectedCayleyGraph S ≃g undirectedCayleyGraph T) →
    relatedByGroupAutomorphism S T

/-- The admitted claim that the dihedral group of order ten is an undirected
    CI-group. -/
def d10IsUndirectedCIGroup : Prop :=
  Fintype.card (DihedralGroup 5) = 10 ∧
    isFiniteUndirectedCIGroup (DihedralGroup 5)

end MathlibPlus.Open.GraphCI
