import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory.SubcutoffMangoldt

/-- For `2 ≤ n ≤ M`, the cutoff at `M` contains every divisor of `n`, and the
Möbius-weighted logarithmic sum is exactly the von Mangoldt coefficient. -/
theorem exact_subcutoff_mangoldt_core
    {n M : ℕ} (hn : 2 ≤ n) (hnM : n ≤ M) :
    (∑ d ∈ (Nat.divisors n).filter (fun d => d ≤ M),
        (ArithmeticFunction.moebius d : ℝ) *
          (1 - Real.log (d : ℝ) / Real.log (M : ℝ))) =
      ArithmeticFunction.vonMangoldt n / Real.log (M : ℝ) := by
  have hnpos : 0 < n := by omega
  have hfilter : (Nat.divisors n).filter (fun d => d ≤ M) = Nat.divisors n := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact le_trans (Nat.le_of_dvd hnpos (Nat.dvd_of_mem_divisors hd)) hnM
  rw [hfilter]
  have hn1 : n ≠ 1 := by omega
  have hmu :
      (∑ d ∈ Nat.divisors n, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
      (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ))
    rw [ArithmeticFunction.coe_zeta_mul_apply] at h
    simpa [hn1] using h
  have hlog :
      (∑ d ∈ Nat.divisors n,
        (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) =
        -ArithmeticFunction.vonMangoldt n := by
    simpa [ArithmeticFunction.log_apply] using
      (ArithmeticFunction.sum_moebius_mul_log_eq (n := n))
  have hM : 1 < M := by omega
  have hlogM : Real.log (M : ℝ) ≠ 0 := by
    exact (ne_of_gt (Real.log_pos (by exact_mod_cast hM)))
  simp only [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, hmu, hlog]
  ring

end MathlibPlus.NumberTheory.SubcutoffMangoldt
