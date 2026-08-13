import Mathlib

namespace MathlibPlus.Analysis.Claim9967

/-- Literal logarithmic-derivative identity from claim 9967.  The source's
parameter `λ = 1/(2√2)` does not occur in the displayed formula, so the
formal statement retains the displayed `t = 2^(-s)` identity without
silently assigning `λ` an additional role. -/
theorem normalizedLogDerivative_claim9967 (s : ℝ) :
    let t : ℝ := (2 : ℝ) ^ (-s);
    -(deriv
        (fun u : ℝ =>
          Real.log
            ((1 + (2 : ℝ) ^ (-u) + 2 * ((2 : ℝ) ^ (-u)) ^ 2) /
              (1 + 2 * ((2 : ℝ) ^ (-u)) ^ 2))) s) =
      Real.log 2 * (t - 2 * t ^ 3) /
        (1 + t + 4 * t ^ 2 + 2 * t ^ 3 + 4 * t ^ 4) := by
  dsimp
  let f : ℝ → ℝ := fun x => (2 : ℝ) ^ (-x)
  let one : ℝ → ℝ := fun _ => 1
  let two : ℝ → ℝ := fun _ => 2
  have hf : HasDerivAt f (Real.log 2 * (-1 : ℝ) * f s) s := by
    simpa [f] using
      (hasDerivAt_id s).neg.const_rpow (by norm_num : (0 : ℝ) < 2)
  have hone : HasDerivAt one 0 s := by
    simpa [one] using (hasDerivAt_const s (1 : ℝ))
  have htwo : HasDerivAt two 0 s := by
    simpa [two] using (hasDerivAt_const s (2 : ℝ))
  have hf2 := hf.mul hf
  have htwof2 := htwo.mul hf2
  have hnum := (hone.add hf).add htwof2
  have hden := hone.add htwof2
  have hfpos : 0 < f s := by
    dsimp [f]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hnumpos : 0 < ((one + f) + two * (f * f)) s := by
    dsimp [one, two]
    positivity
  have hdenpos : 0 < (one + two * (f * f)) s := by
    dsimp [one, two]
    positivity
  have hlog :=
    (hnum.div hden (ne_of_gt hdenpos)).log
      (ne_of_gt (div_pos hnumpos hdenpos))
  have hderiv := hlog.deriv
  have hneg := congrArg (fun x : ℝ => -x) hderiv
  have hfun :
      (fun x : ℝ =>
        Real.log
          ((1 + (2 : ℝ) ^ (-x) + 2 * ((2 : ℝ) ^ (-x)) ^ 2) /
            (1 + 2 * ((2 : ℝ) ^ (-x)) ^ 2))) =
      (fun x : ℝ => Real.log (((one + f) x + (two * (f * f)) x) /
        (one + two * (f * f)) x)) := by
    funext x
    simp [f, one, two, pow_two]
  rw [hfun]
  convert hneg using 1
  dsimp [f, one, two] at hneg ⊢
  simp only [one, two, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply,
    zero_mul, zero_add, add_zero] at hneg ⊢
  field_simp
  ring

end MathlibPlus.Analysis.Claim9967
