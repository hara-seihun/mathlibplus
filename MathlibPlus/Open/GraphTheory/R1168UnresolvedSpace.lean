import MathlibPlus.Open.GraphTheory.R1168TranslationProfile

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.R1168

abbrev Profile := Base → ZMod 7

def baseRoot : Base := (0, 0)

def baseA (z : Base) : Base :=
  (z.1 + if z.2.1 % 2 = 1 then -1 else 1, z.2)

def baseAInv (z : Base) : Base :=
  (z.1 + if z.2.1 % 2 = 1 then 1 else -1, z.2)

def fin8Shift (i : Fin 8) (k : ℕ) : Fin 8 :=
  Fin.ofNat 8 (i.1 + k)

def baseB (z : Base) : Base := (z.1, fin8Shift z.2 1)

def baseBInv (z : Base) : Base :=
  (z.1, Fin.ofNat 8 (z.2.1 + 7))

def baseQ0 (z : Base) : Base := (z.1, baseAction z.2)

def baseB2 (z : Base) : Base := baseQ0 (baseB (baseQ0 z))

def baseB2Inv (z : Base) : Base := baseQ0 (baseBInv (baseQ0 z))

def baseGenerator (k : Fin 6) : Base → Base :=
  ![baseA, baseB, baseB2, baseAInv, baseBInv, baseB2Inv] k

def inverseLetter (k : Fin 6) : Fin 6 :=
  ![3, 4, 5, 0, 1, 2] k

def baseWordValue : List (Fin 6) → Base → Base
  | [], z => z
  | k :: w, z => baseGenerator k (baseWordValue w z)

def inverseWord (w : List (Fin 6)) : List (Fin 6) :=
  w.reverse.map inverseLetter

def generatedBaseMap : Set (Base → Base) :=
  {g | ∃ w : List (Fin 6), ∀ z, baseWordValue w z = g z}

def profileAverage (s : Profile) : ZMod 7 :=
  (Fintype.card Base : ZMod 7)⁻¹ * ∑ z : Base, s z

def paritySign (z : Base) : ZMod 7 :=
  if z.2.1 % 2 = 1 then -1 else 1

def unresolvedEquationAt (s : Profile) (z : Base) : Prop :=
  ∀ w : List (Fin 6),
    let inverseAction := baseWordValue (inverseWord w)
    s (inverseAction z) - paritySign z * s (inverseAction baseRoot) +
        (paritySign z - 1) * profileAverage s = 0

def standardOddFiber : Base := (0, 1)

def standardOddUnresolvedSpace : Set Profile :=
  {s | s baseRoot = 0 ∧ unresolvedEquationAt s standardOddFiber}

def periodTwoProfile (f : ZMod 5 → ZMod 7) : Profile :=
  fun z =>
    if z.2.1 % 2 = 1 then f z.1 else f 0 - f (-z.1)

/-- The standard odd solution space is defined by the explicit affine-Schreier
 equations on the source base action, rather than by the period-two formula. -/
def standardOddUnresolvedNullspace_31792 : Prop :=
  Set.Finite generatedBaseMap ∧
    (∀ g, g ∈ generatedBaseMap → Function.Bijective g) ∧
    Set.ncard generatedBaseMap = 80 ∧
    Set.Finite standardOddUnresolvedSpace ∧
    Set.ncard standardOddUnresolvedSpace = 7 ^ 5 ∧
    (∀ s : Profile,
      s ∈ standardOddUnresolvedSpace ↔
        ∃ f : ZMod 5 → ZMod 7, s = periodTwoProfile f)

end MathlibPlus.Open.GraphTheory.R1168
