import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.LinearAlgebra.Claim50610FallingTransform

noncomputable def fallingFactorial {K : Type*} [Field K]
    (x : K) (k : ℕ) : K :=
  ∏ i ∈ Finset.range k, (x - (i : K))

noncomputable def fallingTransformMatrix {K : Type*} [Field K] [CharZero K]
    (ell : K) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun j r =>
    if h : r ≤ j then
      (-1 : K) ^ (r : ℕ) * (Nat.factorial (r : ℕ) : K) *
        (Nat.choose (j : ℕ) (r : ℕ) : K) *
        fallingFactorial (ell - (r : K)) (j - r)
    else 0

/-- Claim 50610: the exact falling-factorial transform from the A-vector to
 the P-vector is triangular with nonzero diagonal, so the finite vectors
 determine one another over characteristic zero. -/
def claim50610_fallingFactorialTransform : Prop :=
  ∀ {K : Type*} [Field K] [CharZero K]
    (ell : K) (m : ℕ),
    let M := fallingTransformMatrix ell m
    M.det = ∏ i : Fin (m + 1),
        ((-1 : K) ^ (i : ℕ) * (Nat.factorial (i : ℕ) : K)) ∧
      M.det ≠ 0 ∧
        Function.Injective (Matrix.mulVec M)

end MathlibPlus.Open.LinearAlgebra.Claim50610FallingTransform
