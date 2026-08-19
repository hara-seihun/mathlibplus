import Mathlib

namespace MathlibPlus.Open.Research.C2rC9LowValencyClaim61448

noncomputable section
open Classical

/-- The two concrete abelian Cayley-group carriers in Claim 61448. -/
abbrev G61448 (r : ℕ) := (Fin r → ZMod 2) × ZMod 9

abbrev GL61448 (r : ℕ) :=
  (Fin r → ZMod 2) ≃ₗ[ZMod 2] (Fin r → ZMod 2)

abbrev C9Aut61448 := ZMod 9 ≃+ ZMod 9

/-- The product action of `GL(r,2) × Aut(C₉)` on the displayed group. -/
def productAutMap61448 {r : ℕ}
    (φ : GL61448 r) (ψ : C9Aut61448) : G61448 r → G61448 r :=
  fun x => (φ x.1, ψ x.2)

/-- Identity-free and inverse-closed finite connection sets. -/
def identityFree61448 {r : ℕ} (S : Finset (G61448 r)) : Prop :=
  (0 : G61448 r) ∉ S

def inverseClosed61448 {r : ℕ} (S : Finset (G61448 r)) : Prop :=
  ∀ x : G61448 r, x ∈ S → -x ∈ S

def ordinaryConnectionSet61448 {r : ℕ} (S : Finset (G61448 r)) : Prop :=
  identityFree61448 S ∧ inverseClosed61448 S

/-- Adjacency in the ordinary undirected Cayley graph. -/
def cayleyAdj61448 {r : ℕ}
    (S : Finset (G61448 r)) (x y : G61448 r) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Isomorphism of the two finite Cayley graphs on their common vertex set. -/
def cayleyGraphIso61448 {r : ℕ}
    (S T : Finset (G61448 r)) : Prop :=
  ∃ e : G61448 r ≃ G61448 r,
    ∀ x y : G61448 r,
      cayleyAdj61448 S x y ↔ cayleyAdj61448 T (e x) (e y)

/-- The exact connection-set image under the product automorphism. -/
def productAutMapsSet61448 {r : ℕ}
    (φ : GL61448 r) (ψ : C9Aut61448) (S T : Finset (G61448 r)) : Prop :=
  S.image (productAutMap61448 φ ψ) = T

/-- CI for one finite connection set, with the source's full target class. -/
def ciConnectionSet61448 {r : ℕ} (S : Finset (G61448 r)) : Prop :=
  ordinaryConnectionSet61448 S ∧
    ∀ T : Finset (G61448 r),
      ordinaryConnectionSet61448 T →
        cayleyGraphIso61448 S T →
          ∃ φ : GL61448 r, ∃ ψ : C9Aut61448,
            productAutMapsSet61448 φ ψ S T

/-- The finite carrier of every ordinary connection set of valency `k`. -/
def allConnectionSets61448 (r k : ℕ) : Finset (Finset (G61448 r)) :=
  (Finset.univ : Finset (Finset (G61448 r))).filter
    (fun S => ordinaryConnectionSet61448 S ∧ S.card = k)

/-- One-step equivalence of finite connection sets under exactly the
product automorphisms `GL(r,2) × Aut(C₉)`. -/
def productAutEquivalent61448 {r : ℕ}
    (S T : Finset (G61448 r)) : Prop :=
  ∃ φ : GL61448 r, ∃ ψ : C9Aut61448,
    productAutMapsSet61448 φ ψ S T

/-- Quotient carrier for product-automorphism orbits of finite connection sets.
`EqvGen` supplies the equivalence closure of the displayed concrete action. -/
abbrev productAutOrbitQuotient61448 (r : ℕ) :=
  Quotient (Relation.EqvGen.setoid (productAutEquivalent61448 (r := r)))

noncomputable def productAutOrbitClasses61448
    (r k : ℕ) : Finset (productAutOrbitQuotient61448 r) :=
  (allConnectionSets61448 r k).image
    (fun S => Quotient.mk (Relation.EqvGen.setoid
      (productAutEquivalent61448 (r := r))) S)

noncomputable def productAutOrbitCount61448 (r k : ℕ) : ℕ :=
  (productAutOrbitClasses61448 r k).card

/-- The actual ordered-edge carrier of an ordinary Cayley graph. -/
def cayleyEdgeSet61448 {r : ℕ}
    (S : Finset (G61448 r)) : Finset (G61448 r × G61448 r) :=
  (Finset.univ : Finset (G61448 r × G61448 r)).filter
    (fun e => cayleyAdj61448 S e.1 e.2)

/-- Quotient carrier for ordinary graph-isomorphism classes.  The
relation is on the concrete connection-set carrier, so its classes retain
exactly the Cayley adjacency relation rather than detached class labels. -/
def graphEquivalent61448 {r : ℕ}
    (S T : Finset (G61448 r)) : Prop :=
  cayleyGraphIso61448 S T

abbrev graphClassQuotient61448 (r : ℕ) :=
  Quotient (Relation.EqvGen.setoid (graphEquivalent61448 (r := r)))

noncomputable def graphClassValues61448
    (r k : ℕ) : Finset (graphClassQuotient61448 r) :=
  (allConnectionSets61448 r k).image
    (fun S => Quotient.mk (Relation.EqvGen.setoid
      (graphEquivalent61448 (r := r))) S)

noncomputable def graphClassCount61448 (r k : ℕ) : ℕ :=
  (graphClassValues61448 r k).card

/-- A row of the finite low-valency orbit/class census. -/
def censusRow61448 (r k expectedOrbits expectedGraphs : ℕ) : Prop :=
  productAutOrbitCount61448 r k = expectedOrbits ∧
    graphClassCount61448 r k = expectedGraphs

/-- Claim 61448: the rank-four and rank-five low/co-valency windows are
complete CI classifications, with the exact orbit and graph-class counts
reported in the finite replay. -/
def claim61448_c2rC9LowValencyCI : Prop :=
  Fintype.card (G61448 4) = 144 ∧
    Fintype.card (G61448 5) = 288 ∧
    (∀ S : Finset (G61448 4),
      ordinaryConnectionSet61448 S →
        min S.card (143 - S.card) ≤ 12 → ciConnectionSet61448 S) ∧
    (∀ S : Finset (G61448 5),
      ordinaryConnectionSet61448 S →
        min S.card (287 - S.card) ≤ 10 → ciConnectionSet61448 S) ∧
    censusRow61448 4 1 1 1 ∧
    censusRow61448 4 2 5 5 ∧
    censusRow61448 4 3 8 8 ∧
    censusRow61448 4 4 25 25 ∧
    censusRow61448 4 5 52 52 ∧
    censusRow61448 4 6 151 151 ∧
    censusRow61448 4 7 364 364 ∧
    censusRow61448 4 8 1031 1031 ∧
    censusRow61448 4 9 2771 2771 ∧
    censusRow61448 4 10 7988 7988 ∧
    censusRow61448 4 11 22718 22718 ∧
    censusRow61448 4 12 66384 66384 ∧
    censusRow61448 5 1 1 1 ∧
    censusRow61448 5 2 5 5 ∧
    censusRow61448 5 3 8 8 ∧
    censusRow61448 5 4 25 25 ∧
    censusRow61448 5 5 53 53 ∧
    censusRow61448 5 6 157 157 ∧
    censusRow61448 5 7 394 394 ∧
    censusRow61448 5 8 1172 1172 ∧
    censusRow61448 5 9 3421 3421 ∧
    censusRow61448 5 10 10963 10963

end

end MathlibPlus.Open.Research.C2rC9LowValencyClaim61448
