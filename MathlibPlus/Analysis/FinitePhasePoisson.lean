import Mathlib

open scoped ComplexConjugate

namespace MathlibPlus.Analysis

/-- Claim 10125: the finite phase-pair Poisson-square identity. -/
theorem finitePhasePairPoissonSquare
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (ω : ι → ℂ) (x : ℝ) :
    Complex.exp (-(x : ℂ)) *
        (∑' n : ℕ,
          (∑ j, (m j : ℂ) * (ω j)^n) *
            star (∑ j, (m j : ℂ) * (ω j)^n) *
            (x : ℂ)^n / n.factorial) =
      ∑ j, ∑ k,
        ((m j : ℂ) * (m k : ℂ)) *
          Complex.exp ((x : ℂ) * (ω j * star (ω k) - 1)) := by
  rw [Complex.exp_eq_exp_ℂ]
  have hcore :
      ∑' n : ℕ,
          (∑ j, (m j : ℂ) * (ω j)^n) *
            star (∑ j, (m j : ℂ) * (ω j)^n) *
            (x : ℂ)^n / n.factorial =
        ∑ j, ∑ k,
          ((m j : ℂ) * (m k : ℂ)) *
            NormedSpace.exp ((x : ℂ) * (ω j * star (ω k))) := by
    have hjk (j k : ι) :
        HasSum
          (fun n : ℕ =>
            ((m j : ℂ) * (m k : ℂ)) *
              ((x : ℂ) * (ω j * star (ω k))) ^ n / n.factorial)
          (((m j : ℂ) * (m k : ℂ)) *
            NormedSpace.exp ((x : ℂ) * (ω j * star (ω k)))) := by
      have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ)
        ((x : ℂ) * (ω j * star (ω k)))
      apply (h.mul_left ((m j : ℂ) * (m k : ℂ))).congr_fun
      intro n
      simp only [Algebra.smul_def, div_eq_mul_inv, mul_pow]
      norm_num
      ring
    have hk (j : ι) :
        HasSum
          (fun n : ℕ => ∑ k, ((m j : ℂ) * (m k : ℂ)) *
            ((x : ℂ) * (ω j * star (ω k))) ^ n / n.factorial)
          (∑ k, ((m j : ℂ) * (m k : ℂ)) *
            NormedSpace.exp ((x : ℂ) * (ω j * star (ω k)))) := by
      apply hasSum_sum
      intro k hk
      exact hjk j k
    have hj :
        HasSum
          (fun n : ℕ => ∑ j, ∑ k, ((m j : ℂ) * (m k : ℂ)) *
            ((x : ℂ) * (ω j * star (ω k))) ^ n / n.factorial)
          (∑ j, ∑ k, ((m j : ℂ) * (m k : ℂ)) *
            NormedSpace.exp ((x : ℂ) * (ω j * star (ω k)))) := by
      apply hasSum_sum
      intro j hj
      exact hk j
    have hpointwise (n : ℕ) :
        (∑ j, (m j : ℂ) * (ω j)^n) *
            star (∑ j, (m j : ℂ) * (ω j)^n) * (x : ℂ)^n / n.factorial =
          (∑ j, ∑ k, ((m j : ℂ) * (m k : ℂ)) *
            ((x : ℂ) * (ω j * star (ω k))) ^ n) / n.factorial := by
      rw [star_sum]
      simp [star_mul, star_pow]
      simp only [Finset.mul_sum, Finset.sum_mul]
      have hfac : (n.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      rw [div_eq_div_iff hfac hfac]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_pow]
      ring_nf
    rw [← hj.tsum_eq]
    apply tsum_congr
    intro n
    rw [hpointwise n, Finset.sum_div]
    simp_rw [← Finset.sum_div]
  rw [hcore]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  calc
    NormedSpace.exp (-(x : ℂ)) * (((m j : ℂ) * (m k : ℂ)) *
          NormedSpace.exp ((x : ℂ) * (ω j * star (ω k)))) =
        ((m j : ℂ) * (m k : ℂ)) *
          (NormedSpace.exp (-(x : ℂ)) *
            NormedSpace.exp ((x : ℂ) * (ω j * star (ω k)))) := by ring
    _ = ((m j : ℂ) * (m k : ℂ)) *
          NormedSpace.exp (-(x : ℂ) + (x : ℂ) * (ω j * star (ω k))) := by
      rw [NormedSpace.exp_add]
    _ = ((m j : ℂ) * (m k : ℂ)) *
          NormedSpace.exp ((x : ℂ) * (ω j * star (ω k) - 1)) := by
      congr 2
      ring

end MathlibPlus.Analysis
