import Mathlib

namespace MathlibPlus.Open.GraphTheory

noncomputable section
open Classical

/-- The four vertices of the path `0-1-2-3`. -/
abbrev P4Vertex_claim50757 := Fin 4

/-- Adjacency in the labelled path `P₄`. -/
def p4Adj_claim50757
    (u v : P4Vertex_claim50757) : Prop :=
  u.val + 1 = v.val ∨ v.val + 1 = u.val

/-- The common-neighbour set in the explicit labelled path. -/
def p4CommonNeighbors_claim50757
    (u v : P4Vertex_claim50757) : Finset P4Vertex_claim50757 :=
  Finset.univ.filter (fun w =>
    p4Adj_claim50757 w u ∧ p4Adj_claim50757 w v)

/-- The common-neighbour count in `P₄`. -/
def p4CommonNeighborCount_claim50757
    (u v : P4Vertex_claim50757) : Nat :=
  (p4CommonNeighbors_claim50757 u v).card

/-- The set of all common-neighbour values on distinct vertex pairs. -/
def p4CommonNeighborValues_claim50757 : Finset Nat :=
  (Finset.univ : Finset (P4Vertex_claim50757 × P4Vertex_claim50757)).filter
    (fun pair => pair.1 ≠ pair.2) |>.image
      (fun pair => p4CommonNeighborCount_claim50757 pair.1 pair.2)

/-- The card adjacency obtained by deleting the labelled vertex `1`. -/
def p4DeletedOneAdj_claim50757
    (u v : P4Vertex_claim50757) : Prop :=
  u ≠ 1 ∧ v ≠ 1 ∧ p4Adj_claim50757 u v

/-- The card permutation fixing the deleted label and swapping `2,3`. -/
def p4CardPermutation_claim50757 : Equiv.Perm P4Vertex_claim50757 :=
  Equiv.swap (2 : P4Vertex_claim50757) (3 : P4Vertex_claim50757)

/-- The attachment bit from a surviving vertex to the deleted vertex `1`. -/
def p4AttachmentBit_claim50757
    (u : P4Vertex_claim50757) : Nat :=
  if p4Adj_claim50757 1 u then 1 else 0

/-- The attachment bit after applying the card permutation. -/
def p4TransportedAttachmentBit_claim50757
    (u : P4Vertex_claim50757) : Nat :=
  if p4Adj_claim50757 1 (p4CardPermutation_claim50757 u) then 1 else 0

/-- Claim 50757: the explicit P₄ boundary fixture.  The permutation is a
card automorphism with the deleted-label extension convention, but it is not
a global path automorphism; the indicated pair and attachment products both
change from one to zero.  One graph is used throughout, so this is not a deck
collision.
-/
def p4PremiseMatchedGapFailure_claim50757 : Prop :=
  p4CommonNeighborValues_claim50757 = {0, 1} ∧
    p4CardPermutation_claim50757 1 = 1 ∧
    p4CardPermutation_claim50757 2 = 3 ∧
    p4CardPermutation_claim50757 3 = 2 ∧
    (∀ u v : P4Vertex_claim50757,
      p4DeletedOneAdj_claim50757 u v ↔
        p4DeletedOneAdj_claim50757
          (p4CardPermutation_claim50757 u)
          (p4CardPermutation_claim50757 v)) ∧
    (∃ u v : P4Vertex_claim50757,
      p4Adj_claim50757 u v ∧
        ¬ p4Adj_claim50757
          (p4CardPermutation_claim50757 u)
          (p4CardPermutation_claim50757 v)) ∧
    p4CommonNeighborCount_claim50757 0 2 = 1 ∧
    p4CommonNeighborCount_claim50757
      (p4CardPermutation_claim50757 0)
      (p4CardPermutation_claim50757 2) = 0 ∧
    p4AttachmentBit_claim50757 0 * p4AttachmentBit_claim50757 2 = 1 ∧
    p4TransportedAttachmentBit_claim50757 0 *
        p4TransportedAttachmentBit_claim50757 2 = 0

end
end MathlibPlus.Open.GraphTheory
