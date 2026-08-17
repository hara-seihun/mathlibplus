import Mathlib

open Classical
open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R0392

noncomputable section

private abbrev Trace (r : ℕ) := Finset (Fin r)
private abbrev TraceTable (r : ℕ) := Trace r → ℕ

private def rootSet {r n : ℕ} (t : Fin r → Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin r)).image t

private def neighborhoodTrace {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) (v : Fin n) : Trace r :=
  (Finset.univ : Finset (Fin r)).filter (fun i => G.Adj (t i) v)

private def outsideTable {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) : TraceTable r :=
  fun S =>
    ((Finset.univ : Finset (Fin n)).filter (fun v =>
      v ∉ rootSet t ∧ neighborhoodTrace G t v = S)).card

private def internalRootGraph {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) : SimpleGraph (Fin r) :=
  SimpleGraph.fromRel (fun i j => G.Adj (t i) (t j))

private def rootedProfile {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (x : TraceTable r)
    (t : Fin r → Fin n) : Prop :=
  Function.Injective t ∧ internalRootGraph G t = A ∧ outsideTable G t = x

private def rootedTableCoordinate {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (x : TraceTable r) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin n)).filter
    (rootedProfile G A x)).card

private def deletedOutsideTable {r n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (t : Fin r → Fin n) : TraceTable r :=
  fun S =>
    ((Finset.univ : Finset (Fin n)).filter (fun w =>
      w ≠ v ∧ w ∉ rootSet t ∧ neighborhoodTrace G t w = S)).card

private def deletedRootedProfile {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (v : Fin n) (z : TraceTable r)
    (t : Fin r → Fin n) : Prop :=
  Function.Injective t ∧
    (∀ i : Fin r, t i ≠ v) ∧
    internalRootGraph G t = A ∧ deletedOutsideTable G v t = z

private def summedCardSource {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (z : TraceTable r) : ℕ :=
  ∑ v : Fin n,
    ((Finset.univ : Finset (Fin r → Fin n)).filter
      (deletedRootedProfile G A v z)).card

private def addCell {r : ℕ} (z : TraceTable r) (S : Trace r) : TraceTable r :=
  fun U => z U + if U = S then 1 else 0

private def removeEmpty {r : ℕ} (x : TraceTable r) : TraceTable r :=
  fun S => x S - if S = ∅ then 1 else 0

private def recurrenceNumerator {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (x : TraceTable r) : ℤ :=
  (summedCardSource G A (removeEmpty x) : ℤ) -
    ∑ S : Trace r, if S ≠ ∅ then
      ((x S + 1 : ℕ) : ℤ) *
        (rootedTableCoordinate G A (addCell (removeEmpty x) S) : ℤ)
    else 0

/-- Claim 20830: the positive-empty-cell recurrence and its exact integral
quotient, with the coordinates defined by rooted graph tables and their card
sources. -/
def recurrenceForPositiveEmptyCell_claim20830 : Prop :=
  ∀ (r n : ℕ) (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (x : TraceTable r),
    x ∅ > 0 →
      ∃ q : ℤ,
        recurrenceNumerator G A x = (x ∅ : ℤ) * q ∧
          (rootedTableCoordinate G A x : ℤ) = q

end

end MathlibPlus.Open.Combinatorics.R0392
