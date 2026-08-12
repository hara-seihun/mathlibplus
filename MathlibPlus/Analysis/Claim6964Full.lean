import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- Claim 6964: for a positive `C²` real amplitude and a complex `C²`
signal, the gamma-clock product identity holds at every parameter value.
The local operator `D` is the displayed second-derivative expression, and the
second equality identifies the actual second derivative of `log ∘ r`. -/
theorem gammaClockProductIdentity_claim6964
    (r : ℝ → ℝ) (Y : ℝ → ℂ) (t : ℝ)
    (hr : ∀ x, 0 < r x)
    (hR : ContDiff ℝ 2 r) (hY : ContDiff ℝ 2 Y) :
    let D := fun F : ℝ → ℂ =>
      ‖deriv F t‖ ^ 2 - (deriv (deriv F) t * star (F t)).re
    D (fun x => r x • Y x) =
        (r t)^2 * D Y +
          ((deriv r t)^2 - r t * deriv (deriv r) t) * ‖Y t‖^2 ∧
    D (fun x => r x • Y x) =
        (r t)^2 *
          (D Y - deriv (deriv (fun x => Real.log (r x))) t * ‖Y t‖^2) := by
  dsimp
  have hr0 : r t ≠ 0 := ne_of_gt (hr t)
  have hRdiff : Differentiable ℝ r := hR.differentiable (by norm_num)
  have hYdiff : Differentiable ℝ Y := hY.differentiable (by norm_num)
  have hRderivdiff : Differentiable ℝ (deriv r) :=
    (hR.deriv' (n := (1 : WithTop ℕ∞))).differentiable (by norm_num)
  have hYderivdiff : Differentiable ℝ (deriv Y) :=
    (hY.deriv' (n := (1 : WithTop ℕ∞))).differentiable (by norm_num)
  have hprod_deriv : deriv (fun x => r x • Y x) =
      fun x => r x • deriv Y x + deriv r x • Y x := by
    funext x
    change deriv (r • Y) x = _
    rw [deriv_smul hRdiff.differentiableAt hYdiff.differentiableAt]
  have hprod_deriv2 : deriv (deriv (fun x => r x • Y x)) t =
      r t • deriv (deriv Y) t + deriv r t • deriv Y t +
        (deriv r t • deriv Y t + deriv (deriv r) t • Y t) := by
    rw [hprod_deriv]
    change deriv ((r • deriv Y) + (deriv r • Y)) t = _
    rw [deriv_add]
    · rw [deriv_smul hRdiff.differentiableAt hYderivdiff.differentiableAt]
      rw [deriv_smul hRderivdiff.differentiableAt hYdiff.differentiableAt]
    · exact (hRdiff.differentiableAt.smul hYderivdiff.differentiableAt)
    · exact (hRderivdiff.differentiableAt.smul hYdiff.differentiableAt)
  have hprod_first : deriv (fun x => r x • Y x) t =
      r t • deriv Y t + deriv r t • Y t := by
    rw [hprod_deriv]
  have hlog_deriv : deriv (fun x => Real.log (r x)) =
      fun x => deriv r x / r x := by
    funext x
    exact ((hRdiff.differentiableAt).hasDerivAt.log (ne_of_gt (hr x))).deriv
  have hlog_second : deriv (deriv (fun x => Real.log (r x))) t =
      deriv (deriv r) t / r t - (deriv r t / r t)^2 := by
    rw [hlog_deriv]
    change deriv ((deriv r) / r) t = _
    rw [deriv_div hRderivdiff.differentiableAt hRdiff.differentiableAt hr0]
    field_simp [hr0]
  constructor
  · change (‖deriv (fun x => r x • Y x) t‖ ^ 2 -
        (deriv (deriv (fun x => r x • Y x)) t * star (r t • Y t)).re) = _
    rw [hprod_first, hprod_deriv2]
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]
    ring
  · change (‖deriv (fun x => r x • Y x) t‖ ^ 2 -
        (deriv (deriv (fun x => r x • Y x)) t * star (r t • Y t)).re) = _
    rw [hprod_first, hprod_deriv2, hlog_second]
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]
    field_simp [hr0]
    ring

end MathlibPlus.Analysis
