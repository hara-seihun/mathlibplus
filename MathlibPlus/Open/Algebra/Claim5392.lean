import Mathlib

namespace MathlibPlus.Open.Algebra.Claim5392

open scoped BigOperators

noncomputable section

/-- The complete homogeneous polynomial in three displayed variables, with
all nonnegative exponent triples of total degree `k` enumerated explicitly. -/
def completeHomogeneous3 {R : Type*} [CommRing R]
    (k : ℕ) (x y z : R) : R :=
  ∑ i ∈ Finset.range (k + 1),
    ∑ j ∈ Finset.range (k - i + 1),
      x ^ i * y ^ j * z ^ (k - i - j)

/-- The Vandermonde matrix whose rows are ordered by `M,B,A`; this ordering
retains the packet's orientation `(A-B)(A-M)(B-M)`. -/
def ternaryVandermondeMatrix {R : Type*} [CommRing R]
    (A B M : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, M, M ^ 2; 1, B, B ^ 2; 1, A, A ^ 2]

/-- The displayed ternary Vandermonde product. -/
def ternaryVandermondeProduct {R : Type*} [CommRing R]
    (A B M : R) : R :=
  (A - B) * (A - M) * (B - M)

/-- Claim 5392: the oriented ternary Vandermonde determinant has the
 displayed product, while `completeHomogeneous3` is the exact finite sum
 over `i + j + ell = k`. -/
def claim5392 : Prop :=
  (∀ {R : Type*} [CommRing R] (A B M : R),
    Matrix.det (ternaryVandermondeMatrix A B M) =
      ternaryVandermondeProduct A B M) ∧
  (∀ {R : Type*} [CommRing R] (k : ℕ) (x y z : R),
    completeHomogeneous3 k x y z =
      ∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k - i + 1),
          x ^ i * y ^ j * z ^ (k - i - j))

end
end MathlibPlus.Open.Algebra.Claim5392
