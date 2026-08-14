import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev V7 := Fin 2 → ZMod 7

def zeroV7 : V7 := 0

def firstV7 : V7 := fun j => if j = (0 : Fin 2) then 1 else 0

def diagonalObstructionPermutation : Fin 3 × V7 → Fin 3 × V7 :=
  fun p =>
    if p.1 = (1 : Fin 3) then
      if p.2 = zeroV7 then (1, firstV7)
      else if p.2 = firstV7 then (1, zeroV7)
      else p
    else p

def diagonalCell (d : V7) : Set ((Fin 3 × V7) × (Fin 3 × V7)) :=
  {q | ∃ x : V7, q = ((0, x), (1, x + d))}

def transposeDiagonalCell (d : V7) : Set ((Fin 3 × V7) × (Fin 3 × V7)) :=
  {q | ∃ x : V7, q = ((1, x + d), (0, x))}

def mapPairSet (f : Fin 3 × V7 → Fin 3 × V7)
    (C : Set ((Fin 3 × V7) × (Fin 3 × V7))) :
    Set ((Fin 3 × V7) × (Fin 3 × V7)) :=
  Set.image (fun q => (f q.1, f q.2)) C

/-- R-4620, S3: the diagonal mark is destroyed in its ordered rectangle by
one within-block transposition, and inverse pairing cannot restore it. -/
def claim53976 : Prop :=
  (∀ x : V7, diagonalObstructionPermutation (0, x) = (0, x)) ∧
  (∀ x : V7, diagonalObstructionPermutation (2, x) = (2, x)) ∧
  diagonalObstructionPermutation (1, zeroV7) = (1, firstV7) ∧
  diagonalObstructionPermutation (1, firstV7) = (1, zeroV7) ∧
  (∀ x : V7, x ≠ zeroV7 → x ≠ firstV7 →
    diagonalObstructionPermutation (1, x) = (1, x)) ∧
  (diagonalObstructionPermutation (1, zeroV7)).2 - zeroV7 = firstV7 ∧
  (diagonalObstructionPermutation (1, firstV7)).2 - firstV7 = -firstV7 ∧
  (∀ d : V7,
    mapPairSet diagonalObstructionPermutation (diagonalCell zeroV7) ≠
      diagonalCell d) ∧
  (∀ d : V7,
    mapPairSet diagonalObstructionPermutation
        (diagonalCell zeroV7 ∪ transposeDiagonalCell zeroV7) ≠
      diagonalCell d ∪ transposeDiagonalCell d)

end MathlibPlus.Open.ResearchFormalization
