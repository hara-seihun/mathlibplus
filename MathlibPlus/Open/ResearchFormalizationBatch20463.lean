import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalizationBatch20463

noncomputable section

/-- The integer indicator corresponding to the adjacency-status bit. -/
def adjacencyBit (ε : Bool) : ℤ :=
  if ε then 1 else 0

def deletedDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (removed : Finset V) (u : V) : ℕ :=
  (Finset.univ.filter (fun w => w ∉ removed ∧ G.Adj u w)).card

def deletedCommonNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (removed : Finset V) (u v : V) : ℕ :=
  (Finset.univ.filter (fun w => w ∉ removed ∧ G.Adj u w ∧ G.Adj v w)).card

/-- The ordered degree-refined pair count in the card obtained by deleting
`removed`; the vertices retain their host labels while the removed vertices
are excluded from every card degree and common-neighbor count. -/
def cardPairProfile {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (removed : Finset V)
    (ε : Bool) (d e c : ℕ) : ℕ :=
  ((Finset.univ.product (Finset.univ : Finset V)).filter (fun p =>
    p.1 ∉ removed ∧ p.2 ∉ removed ∧ p.1 ≠ p.2 ∧
      (G.Adj p.1 p.2 ↔ ε = true) ∧
      deletedDegree G removed p.1 = d ∧
      deletedDegree G removed p.2 = e ∧
      deletedCommonNeighbors G removed p.1 p.2 = c)).card

def pairProfile {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (d e c : ℕ) : ℕ :=
  cardPairProfile G ∅ ε d e c

def deletedPairProfileSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (d e c : ℕ) : ℕ :=
  ∑ v : V, cardPairProfile G {v} ε d e c

/-- Claim 20463: exact deletion counting for the ordered degree-refined
pair profile, with the coefficients interpreted in the integers rather than
by truncated natural subtraction. -/
def claim_20463 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (d e c : ℕ),
    (deletedPairProfileSum G ε d e c : ℤ) =
      (((Fintype.card V : ℤ) - 2 - d - e +
          2 * adjacencyBit ε + c) *
        (pairProfile G ε d e c : ℤ)) +
      (((d : ℤ) + 1 - adjacencyBit ε - c) *
        (pairProfile G ε (d + 1) e c : ℤ)) +
      (((e : ℤ) + 1 - adjacencyBit ε - c) *
        (pairProfile G ε d (e + 1) c : ℤ)) +
      (((c : ℤ) + 1) *
        (pairProfile G ε (d + 1) (e + 1) (c + 1) : ℤ))

end
end MathlibPlus.Open.ResearchFormalizationBatch20463
