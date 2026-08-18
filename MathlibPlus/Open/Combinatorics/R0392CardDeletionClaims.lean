import Mathlib

open Classical
open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R0392

noncomputable section

private abbrev CardDeletionTrace (r : ℕ) := Finset (Fin r)
private abbrev CardDeletionTraceTable (r : ℕ) := CardDeletionTrace r → ℕ

private def cardDeletionRootSet {r n : ℕ} (t : Fin r → Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin r)).image t

private def cardDeletionNeighborhoodTrace {r n : ℕ}
    (G : SimpleGraph (Fin n)) (t : Fin r → Fin n) (v : Fin n) :
    CardDeletionTrace r :=
  (Finset.univ : Finset (Fin r)).filter (fun i => G.Adj (t i) v)

private def cardDeletionOutsideTable {r n : ℕ}
    (G : SimpleGraph (Fin n)) (t : Fin r → Fin n) : CardDeletionTraceTable r :=
  fun S =>
    ((Finset.univ : Finset (Fin n)).filter (fun v =>
      v ∉ cardDeletionRootSet t ∧ cardDeletionNeighborhoodTrace G t v = S)).card

private def cardDeletionInternalRootGraph {r n : ℕ}
    (G : SimpleGraph (Fin n)) (t : Fin r → Fin n) : SimpleGraph (Fin r) :=
  SimpleGraph.fromRel (fun i j => G.Adj (t i) (t j))

private def cardDeletionRootedProfile {r n : ℕ}
    (G : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r))
    (x : CardDeletionTraceTable r) (t : Fin r → Fin n) : Prop :=
  Function.Injective t ∧
    cardDeletionInternalRootGraph G t = A ∧
    cardDeletionOutsideTable G t = x

private def cardDeletionRootedTableCoordinate {r n : ℕ}
    (G : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r))
    (x : CardDeletionTraceTable r) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin n)).filter
    (cardDeletionRootedProfile G A x)).card

private def cardDeletionDeletedOutsideTable {r n : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) (t : Fin r → Fin n) :
    CardDeletionTraceTable r :=
  fun S =>
    ((Finset.univ : Finset (Fin n)).filter (fun w =>
      w ≠ v ∧ w ∉ cardDeletionRootSet t ∧
        cardDeletionNeighborhoodTrace G t w = S)).card

private def cardDeletionDeletedRootedProfile {r n : ℕ}
    (G : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r)) (v : Fin n)
    (z : CardDeletionTraceTable r) (t : Fin r → Fin n) : Prop :=
  Function.Injective t ∧
    (∀ i : Fin r, t i ≠ v) ∧
    cardDeletionInternalRootGraph G t = A ∧
    cardDeletionDeletedOutsideTable G v t = z

private def cardDeletionSummedCardSource {r n : ℕ}
    (G : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r))
    (z : CardDeletionTraceTable r) : ℕ :=
  ∑ v : Fin n,
    ((Finset.univ : Finset (Fin r → Fin n)).filter
      (cardDeletionDeletedRootedProfile G A v z)).card

private def cardDeletionAddCell {r : ℕ}
    (z : CardDeletionTraceTable r) (S : CardDeletionTrace r) :
    CardDeletionTraceTable r :=
  fun U => z U + if U = S then 1 else 0

/-- Claim 20825: an injectively ordered root tuple determines the exact
outside-neighborhood table on the Boolean trace cells, with total outside mass
`n - r`; the fixed internal graph and table are tied to the same rooted profile.
-/
def outsideNeighborhoodTable_claim20825 : Prop :=
  ∀ (r n : ℕ) (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (x : CardDeletionTraceTable r)
    (t : Fin r → Fin n),
    cardDeletionRootedProfile G A x t →
      (∑ S : CardDeletionTrace r, x S) = n - r

/-- Claim 20829: the summed card source of a deleted rooted table equals the
weighted sum of complete rooted-table coordinates obtained by adding one exact
outside trace cell.
-/
def cardDeletionIdentity_claim20829 : Prop :=
  ∀ (r n : ℕ) (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (z : CardDeletionTraceTable r),
    cardDeletionSummedCardSource G A z =
      ∑ S : CardDeletionTrace r,
        (z S + 1) *
          cardDeletionRootedTableCoordinate G A (cardDeletionAddCell z S)

end

end MathlibPlus.Open.Combinatorics.R0392
