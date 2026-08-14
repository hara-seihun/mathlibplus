import Mathlib

open scoped BigOperators Classical

namespace MathlibPlus.Open.GraphTheory

noncomputable section

abbrev F5 := ZMod 5
abbrev V6 := Fin 6 → F5

/-- The first-nonzero-coordinate-one representatives of nonzero projective
linear functionals on `F₅^6`, identified with their coefficient vectors. -/
def isProjectiveRepresentative (a : V6) : Prop :=
  ∃ i : Fin 6, a i = 1 ∧ ∀ j : Fin 6, j < i → a j = 0

def projectiveFunctionals : Finset V6 :=
  (Finset.univ : Finset V6).filter isProjectiveRepresentative

def functionalValue (a x : V6) : F5 :=
  ∑ i : Fin 6, a i * x i

def fibreCounts (S : Finset V6) (a : V6) : Fin 5 → ℕ :=
  fun c => (S.filter (fun x => functionalValue a x = (c.1 : F5))).card

/-- A multiset of five counts is the sorted five-entry fibre-count vector. -/
def fibreCountMultiset (S : Finset V6) (a : V6) : Multiset ℕ :=
  (Finset.univ : Finset (Fin 5)).1.map (fibreCounts S a)

def affineHyperplaneProfile (S : Finset V6) : Multiset (Multiset ℕ) :=
  projectiveFunctionals.1.map (fibreCountMultiset S)

def linearTransport (g : V6 ≃ₗ[F5] V6) (S : Finset V6) : Finset V6 :=
  S.map g.toEquiv.toEmbedding

def pairCount (S : Finset V6) (v : V6) : ℕ :=
  ((S.product S).filter (fun p => p.1 + p.2 = v)).card

def tripleCount (S : Finset V6) (v : V6) : ℕ :=
  (((S.product S).product S).filter (fun p => p.1.1 + p.1.2 + p.2 = v)).card

def pairSumProfile (S : Finset V6) : Multiset ℕ :=
  (Finset.univ : Finset V6).1.map (pairCount S)

def tripleSumProfile (S : Finset V6) : Multiset ℕ :=
  (Finset.univ : Finset V6).1.map (tripleCount S)

def isTwoDimensionalLinearPlane (L : Finset V6) : Prop :=
  0 ∈ L ∧
    (∀ x, x ∈ L → ∀ y, y ∈ L → x + y ∈ L) ∧
    (∀ a : F5, ∀ x, x ∈ L → a • x ∈ L) ∧
    L.card = 25

def twoPlaneProfile (S : Finset V6) : Multiset ℕ :=
  ((Finset.univ : Finset (Finset V6)).filter isTwoDimensionalLinearPlane).1.map
    (fun L => (S.filter (fun x => x ∈ L)).card)

/-- Claim 57376: the affine-hyperplane fibre profile is invariant under every
linear transporter, hence under `GL(V₆)`. -/
def claim57376_affineHyperplaneFibreProfile : Prop :=
  ∀ (S : Finset V6) (g : V6 ≃ₗ[F5] V6),
    affineHyperplaneProfile (linearTransport g S) = affineHyperplaneProfile S

/-- Claim 57377: the ordered pair- and triple-sum profiles are invariant under
linear transport. -/
def claim57377_pairTripleSumConvolutionProfiles : Prop :=
  ∀ (S : Finset V6) (g : V6 ≃ₗ[F5] V6),
    pairSumProfile (linearTransport g S) = pairSumProfile S ∧
      tripleSumProfile (linearTransport g S) = tripleSumProfile S

/-- Claim 57378: the multiset of intersections with two-dimensional linear
planes is invariant under `GL(V₆)`. -/
def claim57378_twoDimensionalLinearPlaneIncidenceProfile : Prop :=
  ∀ (S : Finset V6) (g : V6 ≃ₗ[F5] V6),
    twoPlaneProfile (linearTransport g S) = twoPlaneProfile S

end
end MathlibPlus.Open.GraphTheory
