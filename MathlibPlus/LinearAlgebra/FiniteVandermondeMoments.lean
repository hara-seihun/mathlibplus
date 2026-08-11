import Mathlib

namespace MathlibPlus.LinearAlgebra.FiniteVandermondeMoments

private theorem exp_nodes_injective {m : ℕ} (t : Fin m → ℝ)
    (ht : Function.Injective t) :
    Function.Injective (fun j : Fin m => Real.exp (-t j)) := by
  intro i j hij
  apply ht
  exact neg_injective (Real.exp_injective hij)

theorem exponential_vandermonde_det_ne_zero {m : ℕ} (t : Fin m → ℝ)
    (ht : Function.Injective t) :
    (Matrix.vandermonde (fun j : Fin m => Real.exp (-t j))).det ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  exact exp_nodes_injective t ht

theorem finite_exponential_moment_uniqueness {m : ℕ} (t c : Fin m → ℝ)
    (ht : Function.Injective t)
    (hzero : ∀ r : Fin m,
      ∑ j : Fin m, c j * Real.exp (-((r : ℕ) : ℝ) * t j) = 0) :
    c = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (exp_nodes_injective t ht)
  intro r
  calc
    ∑ j : Fin m, c j * (Real.exp (-t j)) ^ (r : ℕ) =
        ∑ j : Fin m, c j * Real.exp ((r : ℝ) * (-t j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.exp_nat_mul]
    _ = ∑ j : Fin m, c j * Real.exp (-((r : ℝ) * t j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      ring
    _ = 0 := by simpa [neg_mul] using hzero r

end MathlibPlus.LinearAlgebra.FiniteVandermondeMoments
