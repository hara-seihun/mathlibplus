import Mathlib

namespace MathlibPlus.Analysis.Claim14159

private lemma deriv_sq (x : ℝ) :
    deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
  have h := deriv_pow (f := id) (x := x) differentiableAt_id 2
  simpa [id_eq] using h

private lemma deriv_quad (x b : ℝ) :
    deriv (fun y : ℝ => (y ^ 2 - b ^ 2) ^ 2) x =
      4 * x * (x ^ 2 - b ^ 2) := by
  have hi : DifferentiableAt ℝ (fun y : ℝ => y ^ 2 - b ^ 2) x := by
    fun_prop
  have hinner : deriv (fun y : ℝ => y ^ 2 - b ^ 2) x = 2 * x := by
    rw [deriv_sub_const]
    exact deriv_sq x
  have hp := deriv_pow (f := fun y : ℝ => y ^ 2 - b ^ 2) (x := x) hi 2
  change deriv ((fun y : ℝ => y ^ 2 - b ^ 2) ^ 2) x = _
  rw [hp, hinner]
  ring

private lemma quad_ne_zero {x b : ℝ} (h : x ^ 2 - b ^ 2 ≠ 0) :
    (x ^ 2 - b ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h

private lemma quad_factor_ne_zero {x b : ℝ} (h₁ : x ≠ b) (h₂ : x ≠ -b) :
    x ^ 2 - b ^ 2 ≠ 0 := by
  rw [show x ^ 2 - b ^ 2 = (x - b) * (x + b) by ring]
  apply mul_ne_zero (sub_ne_zero.mpr h₁)
  intro h
  apply h₂
  linarith

private lemma deriv_log_quad (x b : ℝ) (h : x ^ 2 - b ^ 2 ≠ 0) :
    deriv (fun y : ℝ => Real.log ((y ^ 2 - b ^ 2) ^ 2)) x =
      4 * x / (x ^ 2 - b ^ 2) := by
  have hq : DifferentiableAt ℝ (fun y : ℝ => (y ^ 2 - b ^ 2) ^ 2) x := by
    fun_prop
  have hq0 : (x ^ 2 - b ^ 2) ^ 2 ≠ 0 := quad_ne_zero h
  have hcomp := deriv_comp x (Real.differentiableAt_log hq0) hq
  change deriv (Real.log ∘ (fun y : ℝ => (y ^ 2 - b ^ 2) ^ 2)) x = _
  rw [hcomp, Real.deriv_log, deriv_quad]
  field_simp [h]

/-- The displayed second logarithmic derivative in admitted claim 14159.

The source notation `log(t^2-b^2)^2` is read as
`log ((t^2-b^2)^2)`, which is the parse matching the displayed identity.
The nonzero-root hypotheses make the classical derivative calculation
well-defined.
-/
theorem lineMember_secondDeriv_claim14159 (t b : ℝ) (ht : t ≠ b)
    (htneg : t ≠ -b) :
    deriv (fun x : ℝ => deriv
      (fun y : ℝ => Real.log ((y ^ 2 - b ^ 2) ^ 2)) x) t =
        -2 / (t - b) ^ 2 - 2 / (t + b) ^ 2 := by
  have hden : t ^ 2 - b ^ 2 ≠ 0 := quad_factor_ne_zero ht htneg
  have hminus : t - b ≠ 0 := sub_ne_zero.mpr ht
  have hplus : t + b ≠ 0 := by
    intro h
    apply htneg
    linarith
  have hnum : DifferentiableAt ℝ (fun x => 4 * x) t := by
    fun_prop
  have hdenfun : DifferentiableAt ℝ (fun x => x ^ 2 - b ^ 2) t := by
    fun_prop
  have hquot := deriv_div hnum hdenfun hden
  have hnum_deriv : deriv (fun x : ℝ => 4 * x) t = 4 := by
    simpa using deriv_const_mul (𝕜 := ℝ) 4 differentiableAt_id
  have hden_deriv : deriv (fun x : ℝ => x ^ 2 - b ^ 2) t = 2 * t := by
    rw [deriv_sub_const]
    exact deriv_sq t
  have hD : deriv (fun x : ℝ => 4 * x / (x ^ 2 - b ^ 2)) t =
      -4 * (t ^ 2 + b ^ 2) / (t ^ 2 - b ^ 2) ^ 2 := by
    change deriv ((fun x : ℝ => 4 * x) / (fun x : ℝ => x ^ 2 - b ^ 2)) t = _
    rw [hquot, hnum_deriv, hden_deriv]
    field_simp [hden]
    ring
  have heq :
      (fun x : ℝ => deriv (fun y : ℝ => Real.log ((y ^ 2 - b ^ 2) ^ 2)) x) =ᶠ[nhds t]
        (fun x : ℝ => 4 * x / (x ^ 2 - b ^ 2)) := by
    filter_upwards [eventually_ne_nhds ht, eventually_ne_nhds htneg] with x hxb hxn
    exact deriv_log_quad x b (quad_factor_ne_zero hxb hxn)
  rw [heq.deriv_eq, hD]
  field_simp [hden, hminus, hplus]
  ring

end MathlibPlus.Analysis.Claim14159
