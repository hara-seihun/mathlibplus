import Mathlib

namespace MathlibPlus.Analysis

open scoped BigOperators

/-- A vanishing positive-length geometric sum has a nontrivial root-of-unity ratio. -/
theorem geometricSum_zero_rootOfUnity_claim10622
    (p : ℝ) (z : ℂ) (R : ℕ)
    (hp : 1 < p) (hR : 1 ≤ R)
    (hsum : ∑ k ∈ Finset.range (R + 1), ((p : ℂ) ^ (-z)) ^ k = 0) :
    ((p : ℂ) ^ (-z)) ^ (R + 1) = 1 ∧
      (p : ℂ) ^ (-z) ≠ 1 ∧
      ‖(p : ℂ) ^ (-z)‖ = 1 ∧ z.re = 0 := by
  let w : ℂ := (p : ℂ) ^ (-z)
  have hsum' : ∑ k ∈ Finset.range (R + 1), w ^ k = 0 := by
    simpa [w] using hsum
  have hn : R + 1 ≠ 0 := by omega
  have hpow_sub : w ^ (R + 1) - 1 = 0 := by
    have hgeom := mul_geom_sum w (R + 1)
    rw [hsum', mul_zero] at hgeom
    exact hgeom.symm
  have hpow : w ^ (R + 1) = 1 := sub_eq_zero.mp hpow_sub
  have hw_ne : w ≠ 1 := by
    intro h
    have hsum_one := hsum'
    rw [h] at hsum_one
    have hzero : (R + 1 : ℂ) = 0 := by
      simpa using hsum_one
    exact_mod_cast hzero
  have hnormpow : ‖w‖ ^ (R + 1) = 1 := by
    rw [← Complex.norm_pow, hpow, norm_one]
  have hnorm : ‖w‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg w) hn).mp hnormpow
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hnorm_cpow : p ^ (-z.re) = 1 := by
    have h := hnorm
    rw [show w = (p : ℂ) ^ (-z) by rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0] at h
    simpa only [Complex.neg_re] using h
  have hpow_eq : p ^ (-z.re) = p ^ (0 : ℝ) := by
    simpa using hnorm_cpow
  have hz : -z.re = (0 : ℝ) :=
    (Real.rpow_right_inj hp0 (ne_of_gt hp)).mp hpow_eq
  exact ⟨by simpa [w] using hpow, by simpa [w] using hw_ne,
    by simpa [w] using hnorm, by linarith⟩

end MathlibPlus.Analysis
