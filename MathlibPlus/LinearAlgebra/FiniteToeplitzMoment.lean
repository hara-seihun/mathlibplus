import Mathlib

/-!
# Finite-divisor Toeplitz moment matrices

The finite divisor is represented, with multiplicity, by a map from a finite type
to nonzero complex points.  The definitions themselves make sense for any finite
complex family; the surrounding divisor application supplies nonvanishing and
inversion--conjugation stability.
-/

namespace MathlibPlus.LinearAlgebra.FiniteToeplitzMoment

open scoped BigOperators

/-- The Laurent monomial moment of a finite complex family. -/
noncomputable def finiteDivisorMoment {m : ℕ}
    (W : Fin m → ℂ) (exponent : ℤ) : ℂ :=
  ∑ r, W r ^ exponent

/-- The order-`N` Toeplitz moment matrix of a finite complex family:
its `(j,k)` entry is the moment of `u^(j-k)`. -/
noncomputable def finiteToeplitzMomentMatrix {m : ℕ}
    (W : Fin m → ℂ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun j k => finiteDivisorMoment W (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))

/-- Entrywise form of the finite Toeplitz moment matrix. -/
theorem finiteToeplitzMomentMatrix_apply {m : ℕ}
    (W : Fin m → ℂ) (N : ℕ) (j k : Fin (N + 1)) :
    finiteToeplitzMomentMatrix W N j k =
      ∑ r, W r ^ (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) := by
  rfl

/-- Claim 4841: a finite geometric series is a two-sided inverse for
`1 - zS` whenever `S` is nilpotent of index at most `n`.

The concrete lower-shift matrix in the claim is covered by this general
nilpotent form once its nilpotence equation `S ^ n = 0` is supplied. -/
theorem nilpotentResolventRepresentation
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (z : ℝ)
    (hS : S ^ n = 0) :
    let T : Matrix (Fin n) (Fin n) ℝ :=
      (Finset.sum (Finset.range n) fun k => z ^ k • S ^ k)
    ((1 - z • S) * T = 1) ∧ (T * (1 - z • S) = 1) := by
  dsimp
  have hX : (z • S) ^ n = 0 := by
    rw [smul_pow, hS, smul_zero]
  have hT :
      (Finset.sum (Finset.range n) fun k => z ^ k • S ^ k) =
        Finset.sum (Finset.range n) fun k => (z • S) ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [smul_pow]
  constructor
  · rw [hT, mul_neg_geom_sum, hX]
    simp
  · rw [hT, geom_sum_mul_neg, hX]
    simp

end MathlibPlus.LinearAlgebra.FiniteToeplitzMoment
