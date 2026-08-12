import Mathlib

namespace MathlibPlus.LinearAlgebra

/--
Claim 7957.  The finite pole matrix factors as a Vandermonde matrix, a
weighted diagonal matrix, and the transpose of the second Vandermonde matrix.
Integer exponents make the negative powers explicit; the nonzero-node
hypothesis is the exact condition used to combine them.
-/
theorem exactVandermondeFactorization_claim7957
    {K : Type*} [Field K] (k : ℕ) (r : ℤ)
    (x c : Fin k → K) (hx : ∀ j, x j ≠ 0) :
    let Q : Matrix (Fin k) (Fin k) K := fun a b =>
      ∑ j, c j * (x j) ^ (r + (b : ℤ) - (a : ℤ))
    let U : Matrix (Fin k) (Fin k) K := fun a j => (x j) ^ (-(a : ℤ))
    let V : Matrix (Fin k) (Fin k) K := fun b j => (x j) ^ (b : ℤ)
    let D : Matrix (Fin k) (Fin k) K := Matrix.diagonal (fun j => c j * (x j) ^ r)
    Q = U * D * Matrix.transpose V := by
  dsimp
  ext a b
  change (∑ j, c j * (x j) ^ (r + (b : ℤ) - (a : ℤ))) =
    ∑ j, (∑ i, (x i) ^ (-(a : ℤ)) *
      (if i = j then c i * (x i) ^ r else 0)) * (x j) ^ (b : ℤ)
  apply Finset.sum_congr rfl
  intro j hj
  have hinner :
      (∑ i, (x i) ^ (-(a : ℤ)) *
        (if i = j then c i * (x i) ^ r else 0)) =
        (x j) ^ (-(a : ℤ)) * (c j * (x j) ^ r) := by
    simp
  rw [hinner]
  have hz :
      (x j) ^ (-(a : ℤ)) * (x j) ^ r * (x j) ^ (b : ℤ) =
        (x j) ^ (r + (b : ℤ) - (a : ℤ)) := by
    rw [← zpow_add₀ (hx j) (-(a : ℤ)) r]
    rw [← zpow_add₀ (hx j) ((-(a : ℤ)) + r) (b : ℤ)]
    congr 1
    ring
  rw [← hz]
  ring

end MathlibPlus.LinearAlgebra
