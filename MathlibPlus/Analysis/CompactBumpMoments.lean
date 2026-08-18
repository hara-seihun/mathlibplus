import Mathlib

namespace MathlibPlus.Analysis.CompactBumpMoments

open Set MeasureTheory
open scoped Interval

/-- The exact finite-interval integration-by-parts identity for the compact bump
moments. The hypothesis says exactly that `φ` is continuously differentiable on
an open neighborhood of the interval joining `0` and `V`. -/
theorem integrationByParts
    (φ : ℝ → ℝ) (V : ℝ) (n : ℕ)
    (hC1 : ∃ s : Set ℝ,
      IsOpen s ∧ Set.uIcc 0 V ⊆ s ∧ ContDiffOn ℝ 1 φ s) :
    (2 / (Nat.factorial (2 * n) : ℝ)) *
        (∫ v in 0..V, deriv φ v * v ^ (2 * n + 1)) =
      2 * φ V * V ^ (2 * n + 1) / (Nat.factorial (2 * n) : ℝ) -
        (2 * (2 * (n : ℝ) + 1) / (Nat.factorial (2 * n) : ℝ)) *
          (∫ v in 0..V, φ v * v ^ (2 * n)) := by
  obtain ⟨s, hs, hsub, hφ⟩ := hC1
  have hφ_deriv : ∀ x ∈ Set.uIcc 0 V, HasDerivAt φ (deriv φ x) x := by
    intro x hx
    exact (hφ.contDiffAt (hs.mem_nhds (hsub hx))).differentiableAt (by norm_num) |>.hasDerivAt
  have hderiv_integrable : IntervalIntegrable (deriv φ) volume 0 V :=
    ((hφ.continuousOn_deriv_of_isOpen hs (by norm_num)).mono hsub).intervalIntegrable
  have hpow_integrable :
      IntervalIntegrable (fun x : ℝ => (2 * n + 1 : ℕ) * x ^ (2 * n)) volume 0 V :=
    (continuous_const.mul (continuous_id.pow (2 * n))).continuousOn.intervalIntegrable
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 0) (b := V)
    (u := fun x : ℝ => x ^ (2 * n + 1))
    (v := φ)
    (u' := fun x : ℝ => (2 * n + 1 : ℕ) * x ^ (2 * n))
    (v' := deriv φ)
    (fun x _ => by simpa using hasDerivAt_pow (2 * n + 1) x)
    hφ_deriv hpow_integrable hderiv_integrable
  have hbase :
      (∫ v in 0..V, deriv φ v * v ^ (2 * n + 1)) =
        φ V * V ^ (2 * n + 1) -
          (2 * (n : ℝ) + 1) * (∫ v in 0..V, φ v * v ^ (2 * n)) := by
    calc
      (∫ v in 0..V, deriv φ v * v ^ (2 * n + 1)) =
          ∫ v in 0..V, v ^ (2 * n + 1) * deriv φ v := by
            apply intervalIntegral.integral_congr
            intro x _
            ring
      _ = V ^ (2 * n + 1) * φ V -
          0 ^ (2 * n + 1) * φ 0 -
            ∫ v in 0..V, ((2 * n + 1 : ℕ) : ℝ) * v ^ (2 * n) * φ v := hip
      _ = φ V * V ^ (2 * n + 1) -
          (2 * (n : ℝ) + 1) * (∫ v in 0..V, φ v * v ^ (2 * n)) := by
            rw [show (∫ v in 0..V, ((2 * n + 1 : ℕ) : ℝ) * v ^ (2 * n) * φ v) =
              (2 * (n : ℝ) + 1) * (∫ v in 0..V, φ v * v ^ (2 * n)) by
                rw [← intervalIntegral.integral_const_mul]
                apply intervalIntegral.integral_congr
                intro x _
                push_cast
                ring]
            simp
            ring
  rw [hbase]
  ring

end MathlibPlus.Analysis.CompactBumpMoments
