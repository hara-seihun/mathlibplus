import Mathlib

namespace MathlibPlus.Open.Combinatorics.R0392Claim20826

open Classical
open scoped BigOperators

noncomputable section

abbrev Trace20826 (r : ℕ) := Finset (Fin r)
abbrev TraceTable20826 (r : ℕ) := Trace20826 r → ℕ

def rootSet20826 {r n : ℕ} (t : Fin r → Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin r)).image t

def neighborhoodTrace20826 {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) (v : Fin n) : Trace20826 r :=
  (Finset.univ : Finset (Fin r)).filter (fun i => G.Adj (t i) v)

def outsideTable20826 {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) : TraceTable20826 r :=
  fun S =>
    ((Finset.univ : Finset (Fin n)).filter (fun v =>
      v ∉ rootSet20826 t ∧ neighborhoodTrace20826 G t v = S)).card

def internalRootGraph20826 {r n : ℕ} (G : SimpleGraph (Fin n))
    (t : Fin r → Fin n) : SimpleGraph (Fin r) :=
  SimpleGraph.fromRel (fun i j => G.Adj (t i) (t j))

def rootedProfile20826 {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (x : TraceTable20826 r)
    (t : Fin r → Fin n) : Prop :=
  Function.Injective t ∧
    internalRootGraph20826 G t = A ∧
      outsideTable20826 G t = x

def properIntersectionCell20826 {r : ℕ} (T : Trace20826 r) : Prop :=
  T.Nonempty ∧ T ≠ (Finset.univ : Finset (Fin r))

def properIntersectionMargin20826 {r : ℕ}
    (x : TraceTable20826 r) (T : Trace20826 r) : ℕ :=
  Finset.sum ((Finset.univ : Finset (Trace20826 r)).filter
    (fun S => T ⊆ S)) (fun S => x S)

def sameProperIntersectionBlock20826 {r : ℕ}
    (x : TraceTable20826 r) (m : TraceTable20826 r) : Prop :=
  ∀ T : Trace20826 r, properIntersectionCell20826 T →
    properIntersectionMargin20826 x T = m T

def properIntersectionBlockTotal20826 {r n : ℕ}
    (G : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r))
    (m : TraceTable20826 r) : ℕ :=
  ∑ t : Fin r → Fin n,
    if rootedProfile20826 G A (outsideTable20826 G t) t ∧
        sameProperIntersectionBlock20826 (outsideTable20826 G t) m then
      1
    else 0

/-- Claim 20826: a proper-intersection block fixes the ordered root size, the
internal root graph, and all nonempty proper common-neighborhood margins; its
block total is the sum of the complete rooted-table coordinates in that
block. -/
def claim20826 {r n : ℕ} (G : SimpleGraph (Fin n))
    (A : SimpleGraph (Fin r)) (m : TraceTable20826 r) (B : ℕ) : Prop :=
  B = properIntersectionBlockTotal20826 G A m

end

end MathlibPlus.Open.Combinatorics.R0392Claim20826
