import Mathlib

namespace MathlibPlus.Open.Combinatorics.R0392Claim20832

open Classical
open scoped BigOperators

noncomputable section

private abbrev Trace20832 (r : ℕ) := Finset (Fin r)
private abbrev TraceTable20832 (r : ℕ) := Trace20832 r → ℕ

private def rootSet20832 {r n : ℕ} (t : Fin r → Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin r)).image t

private def neighborhoodTrace20832 {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) (v : Fin n) : Trace20832 r :=
  (Finset.univ : Finset (Fin r)).filter (fun i => G.Adj (t i) v)

private def outsideTable20832 {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) : TraceTable20832 r :=
  fun S =>
    ((Finset.univ : Finset (Fin n)).filter (fun v =>
      v ∉ rootSet20832 t ∧ neighborhoodTrace20832 G t v = S)).card

private def internalRootGraph20832 {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) : SimpleGraph (Fin r) :=
  SimpleGraph.fromRel (fun i j => G.Adj (t i) (t j))

private def rootedProfile20832 {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (x : TraceTable20832 r)
    (t : Fin r → Fin n) : Prop :=
  Function.Injective t ∧
    internalRootGraph20832 G t = A ∧
      outsideTable20832 G t = x

private def rootedTableCoordinate20832 {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (x : TraceTable20832 r) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin n)).filter
    (rootedProfile20832 G A x)).card

private def deletedOutsideTable20832 {r n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (t : Fin r → Fin n) : TraceTable20832 r :=
  fun S =>
    ((Finset.univ : Finset (Fin n)).filter (fun w =>
      w ≠ v ∧ w ∉ rootSet20832 t ∧ neighborhoodTrace20832 G t w = S)).card

private def deletedRootedProfile20832 {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (v : Fin n) (z : TraceTable20832 r)
    (t : Fin r → Fin n) : Prop :=
  Function.Injective t ∧
    (∀ i : Fin r, t i ≠ v) ∧
      internalRootGraph20832 G t = A ∧
        deletedOutsideTable20832 G v t = z

private def summedCardSource20832 {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (z : TraceTable20832 r) : ℕ :=
  ∑ v : Fin n,
    ((Finset.univ : Finset (Fin r → Fin n)).filter
      (deletedRootedProfile20832 G A v z)).card

def properIntersectionCell20832 {r : ℕ} (T : Finset (Fin r)) : Prop :=
  T.Nonempty ∧ T ≠ (Finset.univ : Finset (Fin r))

def properIntersectionMargin20832 {r : ℕ}
    (x : TraceTable20832 r) (T : Finset (Fin r)) : ℕ :=
  Finset.sum ((Finset.univ : Finset (Finset (Fin r))).filter
    (fun S => T ⊆ S)) (fun S => x S)

def tableMass20832 {r : ℕ} (x : TraceTable20832 r) : ℕ :=
  ∑ S : Finset (Fin r), x S

def sameProperIntersectionBlock20832 {r : ℕ}
    (x : TraceTable20832 r) (m : TraceTable20832 r) : Prop :=
  ∀ T : Finset (Fin r), properIntersectionCell20832 T →
    properIntersectionMargin20832 x T = m T

/-- The total of all complete rooted-table coordinates in one fixed proper-
margin block, written as the equivalent finite sum over ordered root tuples. -/
private def properIntersectionBlockTotal20832 {r n : ℕ}
    (G : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r))
    (m : TraceTable20832 r) : ℕ :=
  ∑ t : Fin r → Fin n,
    if rootedProfile20832 G A (outsideTable20832 G t) t ∧
        sameProperIntersectionBlock20832 (outsideTable20832 G t) m then
      1
    else 0

/-- The summed card profile and every proper-intersection block total determine
all valid ordered `r`-root profile coordinates: positive empty cells are
recovered by descending recurrence, and the block total fixes the possible
empty-cell boundary. -/
def claim20832 : Prop :=
  ∀ (r n : ℕ) (G H : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)),
    (∀ z : TraceTable20832 r,
      summedCardSource20832 G A z = summedCardSource20832 H A z) →
    (∀ m : TraceTable20832 r,
      properIntersectionBlockTotal20832 G A m =
        properIntersectionBlockTotal20832 H A m) →
    (∀ x : TraceTable20832 r,
      tableMass20832 x = n - r →
        0 < x ∅ →
          rootedTableCoordinate20832 G A x =
            rootedTableCoordinate20832 H A x) ∧
      (∀ x : TraceTable20832 r,
        tableMass20832 x = n - r →
          x ∅ = 0 →
            rootedTableCoordinate20832 G A x =
              rootedTableCoordinate20832 H A x)

end
end MathlibPlus.Open.Combinatorics.R0392Claim20832
