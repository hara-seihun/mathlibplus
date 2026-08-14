import Mathlib

namespace MathlibPlus
namespace Open
namespace Graph

/-- Claim 43985: a graph isomorphism onto a subgraph gives a copy with that image. -/
def copy_of_subgraph_iso
    {α β : Type*} [Fintype α] [Fintype β]
    (pattern : SimpleGraph α) (host : SimpleGraph β)
    (image : host.Subgraph) (e : pattern ≃g image.coe) : Prop :=
  ∃ copy : pattern.Copy host,
    copy.toHom = image.hom.comp e.toHom ∧ copy.toSubgraph = image

/-- Claim 43986: copies with a fixed image are equivalent to graph isomorphisms onto it. -/
def copies_with_fixed_image_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (pattern : SimpleGraph α) (host : SimpleGraph β)
    (image : host.Subgraph) : Prop :=
  Nonempty
    ({copy : pattern.Copy host // copy.toSubgraph = image} ≃ (pattern ≃g image.coe))

/-- Claim 43990: automorphisms of a Boolean-labelled graph are the relation-preserving permutations. -/
def boolean_graph_automorphisms_equiv
    (n : ℕ) (adj : Fin n → Fin n → Bool)
    (_loopless : ∀ i, adj i i = false)
    (_symmetric : ∀ i j, adj i j = adj j i) : Prop :=
  let G : SimpleGraph (Fin n) :=
    SimpleGraph.fromRel (fun i j => adj i j = true)
  Nonempty
    ((G ≃g G) ≃
      {σ : Equiv.Perm (Fin n) //
        ∀ i j, adj (σ i) (σ j) = true ↔ adj i j = true})

/-- Claim 44104: the listed degree triples cannot occur under the stated graph hypotheses. -/
def two_degree_graph_43_excludes_list : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (a b m : ℕ),
    (∀ (S : Finset (Fin 43)), S.card = 5 →
      ¬ ∀ (v w : Fin 43),
        v ∈ S → w ∈ S → v ≠ w → G.Adj v w) →
    (∀ (S : Finset (Fin 43)), S.card = 5 →
      ¬ ∀ (v w : Fin 43),
        v ∈ S → w ∈ S → v ≠ w → ¬ G.Adj v w) →
    Set.range (fun v : Fin 43 => Set.ncard (G.neighborSet v)) = ({a, b} : Set ℕ) →
    a < b →
    (Finset.univ.filter (fun v : Fin 43 => Set.ncard (G.neighborSet v) = a)).card = m →
    ¬ (
      (a, b, m) = (18, 19, 37) ∨
      (a, b, m) = (18, 19, 39) ∨
      (a, b, m) = (18, 19, 41) ∨
      (a, b, m) = (18, 20, 38) ∨
      (a, b, m) = (18, 20, 39) ∨
      (a, b, m) = (18, 20, 40) ∨
      (a, b, m) = (18, 20, 41) ∨
      (a, b, m) = (18, 20, 42) ∨
      (a, b, m) = (18, 21, 39) ∨
      (a, b, m) = (18, 21, 41) ∨
      (a, b, m) = (18, 22, 39) ∨
      (a, b, m) = (18, 22, 40) ∨
      (a, b, m) = (18, 22, 41) ∨
      (a, b, m) = (18, 22, 42) ∨
      (a, b, m) = (18, 23, 39) ∨
      (a, b, m) = (18, 23, 41) ∨
      (a, b, m) = (18, 24, 1) ∨
      (a, b, m) = (18, 24, 2) ∨
      (a, b, m) = (18, 24, 3) ∨
      (a, b, m) = (18, 24, 4) ∨
      (a, b, m) = (18, 24, 6) ∨
      (a, b, m) = (18, 24, 37) ∨
      (a, b, m) = (18, 24, 39) ∨
      (a, b, m) = (18, 24, 40) ∨
      (a, b, m) = (18, 24, 41) ∨
      (a, b, m) = (18, 24, 42) ∨
      (a, b, m) = (19, 24, 2) ∨
      (a, b, m) = (19, 24, 4) ∨
      (a, b, m) = (20, 24, 1) ∨
      (a, b, m) = (20, 24, 2) ∨
      (a, b, m) = (20, 24, 3) ∨
      (a, b, m) = (20, 24, 4) ∨
      (a, b, m) = (21, 24, 2) ∨
      (a, b, m) = (21, 24, 4) ∨
      (a, b, m) = (22, 24, 1) ∨
      (a, b, m) = (22, 24, 2) ∨
      (a, b, m) = (22, 24, 3) ∨
      (a, b, m) = (22, 24, 4) ∨
      (a, b, m) = (22, 24, 5) ∨
      (a, b, m) = (23, 24, 2) ∨
      (a, b, m) = (23, 24, 4) ∨
      (a, b, m) = (23, 24, 6))

end Graph
end Open
end MathlibPlus
