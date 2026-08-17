import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

open scoped BigOperators

abbrev SelectorCube := Fin 3 → Bool

def selectorSign (b : Bool) : ℚ :=
  if b then 1 else -1

def selectorUniformAverage (f : SelectorCube → ℚ) : ℚ :=
  (∑ x : SelectorCube, f x) / (Fintype.card SelectorCube : ℚ)

def selectorPointMass (_x : SelectorCube) : ℚ :=
  1 / (Fintype.card SelectorCube : ℚ)

def selectorProductPointMass (_x : SelectorCube) : ℚ :=
  ∏ _i : Fin 3, (1 / 2 : ℚ)

def selectorIndependentUniform : Prop :=
  ∀ x : SelectorCube, selectorPointMass x = selectorProductPointMass x

def selectorR (x : SelectorCube) : ℚ :=
  selectorSign (x 0)

def selectorY (x : SelectorCube) : ℚ :=
  selectorSign (x 1)

def selectorZ (x : SelectorCube) : ℚ :=
  selectorSign (x 2)

def selectorM1 (x : SelectorCube) : ℚ :=
  (selectorY x + selectorZ x) / 2 +
    selectorR x * (selectorY x - selectorZ x) / 2

def selectorM2 (x : SelectorCube) : ℚ :=
  (selectorY x - selectorZ x) / 2 +
    selectorR x * (selectorY x + selectorZ x) / 2

def selectorM1DepthTwo (x : SelectorCube) : ℚ :=
  if x 0 then selectorY x else selectorZ x

def selectorM2DepthTwo (x : SelectorCube) : ℚ :=
  if x 0 then selectorY x else -selectorZ x

def selectorBoolean (f : SelectorCube → ℚ) : Prop :=
  ∀ x : SelectorCube, f x = 1 ∨ f x = -1

def selectorMixture (x : SelectorCube) : ℚ :=
  (selectorM1 x + selectorM2 x) / 2

def selectorCancelledMixture (x : SelectorCube) : ℚ :=
  selectorY x / 2 + selectorR x * selectorY x / 2

def selectorCharacter (S : Finset (Fin 3)) (x : SelectorCube) : ℚ :=
  Finset.prod S (fun i => selectorSign (x i))

def selectorFourierCoefficient (f : SelectorCube → ℚ)
    (S : Finset (Fin 3)) : ℚ :=
  selectorUniformAverage (fun x => f x * selectorCharacter S x)

def selectorNonconstantFourierL1 (f : SelectorCube → ℚ) : ℚ :=
  Finset.sum (Finset.univ.filter (fun S : Finset (Fin 3) => S ≠ ∅))
    (fun S => |selectorFourierCoefficient f S|)

def selectorQuadraticSupport (f : SelectorCube → ℚ) : Finset (Finset (Fin 3)) :=
  Finset.univ.filter (fun S : Finset (Fin 3) =>
    S.card = 2 ∧ selectorFourierCoefficient f S ≠ 0)

def selectorCell (S : Finset (Fin 3)) (x : SelectorCube) :
    Finset SelectorCube :=
  Finset.univ.filter (fun y : SelectorCube =>
    ∀ i ∈ S, y i = x i)

def selectorCellMean (f : SelectorCube → ℚ) (S : Finset (Fin 3))
    (x : SelectorCube) : ℚ :=
  Finset.sum (selectorCell S x) (fun y => f y) /
    (selectorCell S x).card

def selectorCellVariance (f : SelectorCube → ℚ) (S : Finset (Fin 3))
    (x : SelectorCube) : ℚ :=
  Finset.sum (selectorCell S x) (fun y => (f y) ^ 2) /
      (selectorCell S x).card -
    (selectorCellMean f S x) ^ 2

def selectorExpectedPosteriorVariance (f : SelectorCube → ℚ)
    (S : Finset (Fin 3)) : ℚ :=
  selectorUniformAverage (fun x => selectorCellVariance f S x)

def selectorRevealedCoordinates (stage : Fin 3) : Finset (Fin 3) :=
  if stage = 0 then ∅ else if stage = 1 then {0} else {0, 1}

def selectorRevealVariance (stage : Fin 3) : ℚ :=
  selectorExpectedPosteriorVariance selectorMixture
    (selectorRevealedCoordinates stage)

/-- Claim 61090: the uniform three-sign cancellation example, with coordinates
`0`, `1`, and `2` representing `R`, `Y`, and `Z`.  The two displayed formulas
are realized by depth-two trees which query `R` first and then the indicated
branch coordinate.  Fourier support and root-inclusive posterior variance are
computed from the same finite uniform cube. -/
def selectorCancellationClaim61090 : Prop :=
  selectorIndependentUniform ∧
    (selectorBoolean selectorM1 ∧ selectorBoolean selectorM2) ∧
    (∀ x : SelectorCube,
      selectorM1 x = selectorM1DepthTwo x ∧
        selectorM2 x = selectorM2DepthTwo x) ∧
    (∀ x : SelectorCube,
      selectorMixture x = selectorCancelledMixture x) ∧
    selectorQuadraticSupport selectorMixture =
      {{0, 1}} ∧
    selectorNonconstantFourierL1 selectorMixture = 1 ∧
    selectorRevealVariance 0 = 1 / 2 ∧
    selectorRevealVariance 1 = 1 / 2 ∧
    selectorRevealVariance 2 = 0 ∧
    Finset.sum (Finset.univ : Finset (Fin 3)) selectorRevealVariance = 1

end ResearchFormalization
end Open
end MathlibPlus
