import Mathlib

namespace MathlibPlus.Open.Combinatorics.FiniteGraphDeck

/-- Finite simple graphs represented on a canonical finite vertex type. -/
abbrev FiniteGraph := Sigma (fun n : ℕ => SimpleGraph (Fin n))

/-- Isomorphism of finite simple graphs, including graphs of different labels. -/
def graphIsoRel (G H : FiniteGraph) : Prop :=
  Nonempty (G.2 ≃g H.2)

/-- The carrier of unlabelled finite simple graphs. -/
abbrev GraphIsoClass := Quot graphIsoRel

/-- The isomorphism class of a finite simple graph. -/
def graphClass (G : FiniteGraph) : GraphIsoClass := Quot.mk graphIsoRel G

/-- The graph obtained by deleting one vertex and reindexing the remainder. -/
def vertexDeletedGraph : {n : ℕ} → SimpleGraph (Fin n) → Fin n → SimpleGraph (Fin (n - 1))
  | 0, _, v => Fin.elim0 v
  | n + 1, G, v => G.comap (Fin.succAbove v)

/-- The finite graph obtained by deleting one vertex. -/
def deletedFiniteGraph {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : FiniteGraph :=
  ⟨n - 1, vertexDeletedGraph G v⟩

/-- The multiset of isomorphism classes of all vertex-deleted cards. -/
def vertexDeck (G : FiniteGraph) : Multiset GraphIsoClass :=
  match G with
  | ⟨n, g⟩ =>
      (Finset.univ : Finset (Fin n)).val.map
        (fun v => graphClass (deletedFiniteGraph g v))

/-- A leaf is a vertex whose finite neighbor set has cardinality one. -/
def leafVertex {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  letI : Fintype (G.neighborSet v) := Fintype.ofFinite _
  G.degree v = 1

/-- The multiset of isomorphism classes of cards obtained by deleting leaves. -/
noncomputable def leafDeck (G : FiniteGraph) : Multiset GraphIsoClass := by
  classical
  exact match G with
  | ⟨n, g⟩ =>
      ((Finset.univ : Finset (Fin n)).filter (fun v => leafVertex g v)).val.map
        (fun v => graphClass (deletedFiniteGraph g v))

end MathlibPlus.Open.Combinatorics.FiniteGraphDeck
