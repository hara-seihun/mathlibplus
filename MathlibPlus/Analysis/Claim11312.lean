import Mathlib

namespace MathlibPlus.Analysis

/-- For a positive real `u`, the function `x ↦ sinh (u*x) / x` is strictly
increasing on the positive reals. -/
theorem sinh_mul_div_strictMono_claim11312 (u : ℝ) (hu : 0 < u) :
    StrictMonoOn (fun x : ℝ => Real.sinh (u * x) / x) (Set.Ioi 0) := by
  have haux : StrictMonoOn (fun y : ℝ => y * Real.cosh y - Real.sinh y) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) ?_ ?_
    · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro y hy
      rw [interior_Ici] at hy
      change 0 < y at hy
      change 0 < deriv ((id * Real.cosh) - Real.sinh) y
      have hmul_diff : DifferentiableAt ℝ (id * Real.cosh) y :=
        differentiableAt_id.mul Real.differentiableAt_cosh
      rw [deriv_sub hmul_diff Real.differentiableAt_sinh]
      rw [deriv_mul differentiableAt_id Real.differentiableAt_cosh]
      rw [Real.deriv_cosh, Real.deriv_sinh, deriv_id]
      simp only [id_eq]
      nlinarith [Real.sinh_pos_iff.2 hy]
  refine strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) ?_ ?_
  · exact
      ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn.div₀
        continuous_id.continuousOn (by
          intro x hx
          exact ne_of_gt (Set.mem_Ioi.1 hx)))
  · intro x hx
    rw [interior_Ioi] at hx
    have hux : 0 < u * x := mul_pos hu hx
    have hnum : 0 < (u * x) * Real.cosh (u * x) - Real.sinh (u * x) := by
      have h := haux (show (0 : ℝ) ∈ Set.Ici 0 by simp)
        (show u * x ∈ Set.Ici 0 by exact le_of_lt hux) hux
      simpa using h
    have hs := (Real.hasDerivAt_sinh (u * x)).comp x
      (hasDerivAt_const_mul (x := x) u)
    have hquot := hs.div (hasDerivAt_id' x) (ne_of_gt hx)
    rw [show deriv (fun z : ℝ => Real.sinh (u * z) / z) x =
        (Real.cosh (u * x) * u * x - Real.sinh (u * x)) / x ^ 2 by
      change deriv ((Real.sinh ∘ HMul.hMul u) / (fun z : ℝ => z)) x = _
      simpa only [Function.comp_apply, Pi.div_apply, mul_one] using hquot.deriv]
    have hden : 0 < x ^ 2 := sq_pos_of_pos hx
    have hnum' : 0 < Real.cosh (u * x) * u * x - Real.sinh (u * x) := by
      convert hnum using 1
      ring
    exact div_pos hnum' hden

end MathlibPlus.Analysis
