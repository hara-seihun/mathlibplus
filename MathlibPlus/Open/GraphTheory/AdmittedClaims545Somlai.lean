import Mathlib

namespace MathlibPlus.Open.GraphTheory.Batch545Somlai

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev F5 := ZMod 5
abbrev SomlaiX := Fin 4 → F5
abbrev SomlaiY := Fin 2 → F5
abbrev SomlaiAmbient := SomlaiX × SomlaiY

/-- The two scalar polynomials in the projected Somlai map. -/
def somlaiQ (x : SomlaiX) : F5 :=
  ∑ j ∈ Finset.Icc 1 4, (x 2) ^ j * (x 3) ^ (5 - j)

def somlaiR (x : SomlaiX) : F5 :=
  ∑ j ∈ Finset.Icc 0 4, (x 2) ^ j * (x 3) ^ (4 - j)

def somlaiX0 (x : SomlaiX) : F5 := x 1 * somlaiR x

/-- The exact three-coordinate map from Claim 54564. -/
def somlaiMap (x : SomlaiX) : Fin 3 → F5 :=
  ![-somlaiQ x + somlaiX0 x,
    2 * somlaiQ x + 3 * somlaiX0 x,
    somlaiQ x - somlaiX0 x]

def somlaiProjection (k : Fin 3) (v : Fin 3 → F5) : SomlaiY :=
  if k = 0 then ![v 0, v 1]
  else if k = 1 then ![v 0, v 2]
  else ![v 1, v 2]

def projectedSomlaiMap (k : Fin 3) : SomlaiX → SomlaiY :=
  fun x => somlaiProjection k (somlaiMap x)

/-- The local derivative span `H_u` for each of the three projections. -/
def derivativeSpan (k : Fin 3) (u : SomlaiX) : Submodule F5 SomlaiY :=
  Submodule.span F5
    (Set.range (fun x : SomlaiX =>
      projectedSomlaiMap k (x + u) - projectedSomlaiMap k x -
        projectedSomlaiMap k u))

def finsetCoset (H : Submodule F5 SomlaiY) (a : SomlaiY) : Finset SomlaiY :=
  Finset.univ.filter (fun y : SomlaiY => y - a ∈ H)

def isCoset (H : Submodule F5 SomlaiY) (C : Finset SomlaiY) : Prop :=
  ∃ a : SomlaiY, C = finsetCoset H a

def derivativeAtom (k : Fin 3) (A : Finset SomlaiAmbient) : Prop :=
  ∃ (u : SomlaiX) (C : Finset SomlaiY),
    isCoset (derivativeSpan k u) C ∧
      A = C.image (fun y : SomlaiY => (u, y))

def allDerivativeAtoms (k : Fin 3) : Finset (Finset SomlaiAmbient) :=
  Finset.univ.filter (derivativeAtom k)

def atomInversion (A : Finset SomlaiAmbient) : Finset SomlaiAmbient :=
  A.image (fun p : SomlaiAmbient => (-p.1, -p.2))

def derivativeAtomCount (k : Fin 3) : ℕ :=
  (allDerivativeAtoms k).card

def inversePairAtomClassCount (k : Fin 3) : ℕ :=
  (derivativeAtomCount k +
      ((allDerivativeAtoms k).filter (fun A => atomInversion A = A)).card) / 2

def somlaiExceptionalDirections (k : Fin 3) : Finset SomlaiX :=
  Finset.univ.filter (fun u : SomlaiX =>
    projectedSomlaiMap k u ∉ derivativeSpan k u)

def expectedSomlaiExceptionalDirections : Finset SomlaiX :=
  Finset.univ.filter (fun u : SomlaiX =>
    ∃ a t : F5, t ≠ 0 ∧ u = ![a, t, t, t])

/-- Claim 54568: the exact three-projection atom census and the exact
20-direction derivative-span gap. -/
def exactSomlaiAtomCountsAndGap_claim54568 : Prop :=
  ∀ k : Fin 3,
    derivativeAtomCount k = 3625 ∧
      inversePairAtomClassCount k = 1813 ∧
      somlaiExceptionalDirections k = expectedSomlaiExceptionalDirections ∧
      (somlaiExceptionalDirections k).card = 20

def somlaiTriangularMap (k : Fin 3) : SomlaiAmbient → SomlaiAmbient :=
  fun p => (p.1, p.2 + projectedSomlaiMap k p.1)

def derivativeUnion (k : Fin 3) (S : Set SomlaiAmbient) : Prop :=
  ∀ (u : SomlaiX) (y w : SomlaiY),
    (u, y) ∈ S → w - y ∈ derivativeSpan k u → (u, w) ∈ S

def inversePaired (S : Set SomlaiAmbient) : Prop :=
  ∀ p : SomlaiAmbient, p ∈ S ↔ -p ∈ S

def shiftedDerivativeUnion (k : Fin 3) (S : Set SomlaiAmbient) :
    Set SomlaiAmbient :=
  {p | ∃ (u : SomlaiX) (v : SomlaiY),
    (u, v) ∈ S ∧ p = (u, v + projectedSomlaiMap k u)}

def ambientCayleyRelation (S : Set SomlaiAmbient)
    (p q : SomlaiAmbient) : Prop := q - p ∈ S

/-- Claim 54566: the triangular endpoint map transports every inverse-paired
union of full derivative atoms by the displayed fibre shift. -/
def derivativeAtomTriangularTransport_claim54566 : Prop :=
  ∀ k : Fin 3, Function.Bijective (somlaiTriangularMap k) ∧
    ∀ S : Set SomlaiAmbient,
      derivativeUnion k S → inversePaired S →
        ∀ p q : SomlaiAmbient,
          ambientCayleyRelation S p q ↔
            ambientCayleyRelation (shiftedDerivativeUnion k S)
              (somlaiTriangularMap k p) (somlaiTriangularMap k q)

end
end MathlibPlus.Open.GraphTheory.Batch545Somlai
