import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra

open PowerSeries

/-- If `P` first becomes nonzero at degree `d` and `K` has constant coefficient one,
then multiplication by `K` preserves the first nonzero coefficient. -/
theorem firstNonzeroCoeff_mul_claim33944
    {R : Type*} [Semiring R] [Nontrivial R]
    (P K : PowerSeries R) (d : ℕ)
    (hPzero : ∀ n < d, coeff n P = 0)
    (hPd : coeff d P ≠ 0)
    (hK : constantCoeff K = 1) :
    (∀ n < d, coeff n (K * P) = 0) ∧
      coeff d (K * P) = coeff d P ∧ coeff d (K * P) ≠ 0 := by
  have hlead : coeff d (K * P) = coeff d P := by
    rw [PowerSeries.coeff_mul]
    have hmem : (0, d) ∈ Finset.antidiagonal d := by
      rw [Finset.mem_antidiagonal]
      simp
    calc
      (∑ p ∈ Finset.antidiagonal d, coeff p.1 K * coeff p.2 P) =
          coeff (0, d).1 K * coeff (0, d).2 P := by
        apply Finset.sum_eq_single_of_mem (0, d) hmem
        intro p hp hne
        rw [Finset.mem_antidiagonal] at hp
        by_cases hp₂ : p.2 < d
        · rw [hPzero p.2 hp₂, mul_zero]
        · have hp₂eq : p.2 = d := by omega
          have hp₁eq : p.1 = 0 := by omega
          exact False.elim (hne (Prod.ext hp₁eq hp₂eq))
      _ = coeff d P := by
        have hK0 : coeff 0 K = 1 := by
          exact (PowerSeries.coeff_zero_eq_constantCoeff_apply K).trans hK
        simp [hK0]
  refine ⟨?_, hlead, ?_⟩
  · intro n hn
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have hp₂ : p.2 ≤ n := by omega
    rw [hPzero p.2 (lt_of_le_of_lt hp₂ hn), mul_zero]
  · rw [hlead]
    exact hPd

end MathlibPlus.Algebra
