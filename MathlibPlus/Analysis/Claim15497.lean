import MathlibPlus.Basic

open scoped ENNReal lp

namespace MathlibPlus.Analysis

/-- Claim 15497: the standard coordinate vectors in real `ℓ²(ℕ)` have unit
norm and converge weakly to zero.  The source does not choose a scalar field;
this declaration records its displayed coordinate identity over `ℝ`. -/
theorem claim15497_standardBasisWeaklyNull :
    let e : ℕ → lp (fun _ : ℕ => ℝ) 2 := fun j => lp.single 2 j 1
    (∀ j : ℕ, ‖e j‖ = 1) ∧
      ∀ x : lp (fun _ : ℕ => ℝ) 2,
        (∀ j : ℕ, inner ℝ x (e j) = x j) ∧
          Filter.Tendsto (fun j : ℕ => inner ℝ x (e j)) Filter.atTop (nhds 0) := by
  dsimp
  constructor
  · intro j
    rw [lp.norm_single]
    · norm_num
    · norm_num
  · intro x
    have hsquares : Summable (fun j : ℕ => ‖x j‖ ^ 2) := by
      simpa only [Real.rpow_two, ENNReal.toReal_ofNat] using
        ((lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal))
    have hsq : Filter.Tendsto (fun j : ℕ => ‖x j‖ ^ 2)
        Filter.atTop (nhds 0) := by
      simpa only [Nat.cofinite_eq_atTop] using hsquares.tendsto_cofinite_zero
    have hnorm : Filter.Tendsto (fun j : ℕ => ‖x j‖)
        Filter.atTop (nhds 0) := by
      have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
      simpa [Function.comp_def, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
        using hsqrt
    have hx : Filter.Tendsto (fun j : ℕ => x j)
        Filter.atTop (nhds 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).2 hnorm
    constructor
    · intro j
      simp [lp.inner_single_right]
    · simpa [lp.inner_single_right] using hx

end MathlibPlus.Analysis
