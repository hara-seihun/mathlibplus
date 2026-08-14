import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

open scoped BigOperators

/-- The nine exponent cells in the displayed degree-two spherical character. -/
def degreeTwoSphericalCells : Finset (ℤ × ℤ) :=
  ({2, 0, -2} : Finset ℤ).product {2, 0, -2}

def diagonalPauliCells : Finset (ℤ × ℤ) :=
  {(2, 2), (0, 0), (-2, -2)}

def antiDiagonalPauliCells : Finset (ℤ × ℤ) :=
  {(2, -2), (0, 0), (-2, 2)}

def degreeTwoUsedCells : Finset (ℤ × ℤ) :=
  diagonalPauliCells ∪ antiDiagonalPauliCells

/-- Claim 14790: the two Pauli selections omit exactly the four off-alignment cells. -/
def claim14790 : Prop :=
  degreeTwoSphericalCells.card = 9 ∧
    diagonalPauliCells.card = 3 ∧
    antiDiagonalPauliCells.card = 3 ∧
    degreeTwoUsedCells.card = 5 ∧
    degreeTwoSphericalCells \ degreeTwoUsedCells =
      {(2, 0), (0, 2), (0, -2), (-2, 0)}

end MathlibPlus.Open.FormalizationBatch
