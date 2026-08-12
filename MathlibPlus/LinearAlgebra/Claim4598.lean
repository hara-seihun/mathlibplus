import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4598

/-- Claim 4598: the `(r+1) × r` Laurent-indexed block
`[d_(k+j-m)]_(0 ≤ m ≤ r, 0 ≤ j < r)`.  The coefficient sequence is indexed
by `ℤ` so that Laurent exponents are represented without truncation. -/
def deletedRowLaurentBlock {R : Type*} (d : ℤ → R) (r : ℕ) (k : ℤ) :
    Matrix (Fin (r + 1)) (Fin r) R :=
  fun m j => d (k + (j : ℤ) - (m : ℤ))

/-- Claim 4598: `Δ_m^F(r,k)`, the maximal square minor obtained by deleting
row `m` from the preceding rectangular block. -/
def deletedRowExteriorCofactor {R : Type*} [CommRing R]
    (d : ℤ → R) (r : ℕ) (k : ℤ) (m : Fin (r + 1)) : R :=
  ((deletedRowLaurentBlock d r k).submatrix m.succAboveEmb id).det

end MathlibPlus.LinearAlgebra.Claim4598
