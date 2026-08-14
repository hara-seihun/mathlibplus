import Mathlib.Combinatorics.SimpleGraph.Basic

namespace MathlibPlus.Open.GraphTheory

noncomputable section
open Classical

/-- A labeled (not quotient-by-isomorphism) copy of a pattern as a subgraph. -/
def labeledSubgraphCopy {V W : Type*} (P : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) : Prop :=
  ∀ ⦃u v : V⦄, P.Adj u v → H.Adj (e u) (e v)

def copySupport {V W : Type*} [Fintype V] (e : V ↪ W) : Finset W :=
  Finset.univ.image e

def labeledSubgraphCopies {V W : Type*} [Fintype V] [Fintype W]
    (P : SimpleGraph V) (H : SimpleGraph W) : Finset (V ↪ W) :=
  Finset.univ.filter (labeledSubgraphCopy P H)

def copyInDeletedCard {V W : Type*} [Fintype V]
    (e : V ↪ W) (v : W) : Prop :=
  ∀ u : V, e u ≠ v

def copySupportAvoids {V W : Type*} [Fintype V]
    (e : V ↪ W) (v : W) : Prop :=
  v ∉ copySupport e

/--
Claim 44004.  The family is finite and labeled, support cardinality is the
pattern order, and membership in the literal card obtained by deleting a host
vertex is exactly support avoidance.
-/
def finiteLabeledSubgraphCopies_claim44004 : Prop :=
  ∀ (V W : Type*) [Fintype V] [Fintype W]
    (P : SimpleGraph V) (H : SimpleGraph W),
    (∀ e ∈ labeledSubgraphCopies P H,
      (copySupport e).card = Fintype.card V) ∧
    (∀ (e : V ↪ W) (v : W),
      copyInDeletedCard e v ↔ copySupportAvoids e v) ∧
    (∀ v : W,
      (labeledSubgraphCopies P H).filter (fun e => copyInDeletedCard e v) =
        (labeledSubgraphCopies P H).filter (fun e => copySupportAvoids e v))

end
end MathlibPlus.Open.GraphTheory
