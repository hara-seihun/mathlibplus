import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- A concrete quotient-curvature counterexample, using the convention
`Q(f) = -f''(0)/f(0)` to make the source claim's undefined `Q` explicit. -/
theorem separatePositiveCurvaturesNegativeQuotient_claim10956 :
    let Q : (ℝ → ℝ) → ℝ := fun f => -deriv (deriv f) 0 / f 0
    let F : ℝ → ℝ := fun t => Real.exp (-t ^ 2)
    let H : ℝ → ℝ := fun t => Real.exp (-2 * t ^ 2)
    Q F = 2 ∧ Q H = 4 ∧ Q (fun t => F t / H t) = -2 := by
  dsimp
  have hsecond : ∀ c : ℝ,
      deriv (deriv (fun t : ℝ => Real.exp (c * t ^ 2))) 0 = 2 * c := by
    intro c
    have hfirst : ∀ t : ℝ,
        deriv (fun x : ℝ => Real.exp (c * x ^ 2)) t =
          Real.exp (c * t ^ 2) * ((2 * c) * t) := by
      intro t
      have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t ^ (2 - 1) * 1) t :=
        (hasDerivAt_id t).pow 2
      have hinner : HasDerivAt (fun x : ℝ => c * x ^ 2)
          (c * (2 * t ^ (2 - 1) * 1)) t := by
        simpa only [id_eq] using HasDerivAt.const_mul c hsq
      have hexp := hinner.exp
      convert hexp.deriv using 1 <;> ring
    have hderiv' :
        deriv (fun t : ℝ => Real.exp (c * t ^ 2)) =
          (fun t : ℝ => Real.exp (c * t ^ 2)) * (fun t : ℝ => (2 * c) * t) := by
      funext t
      simpa only [Pi.mul_apply] using hfirst t
    have he : HasDerivAt (fun t : ℝ => Real.exp (c * t ^ 2)) 0 0 := by
      have hsq : HasDerivAt (fun x : ℝ => x ^ 2)
          (2 * (0 : ℝ) ^ (2 - 1) * 1) 0 :=
        (hasDerivAt_id 0).pow 2
      have hinner : HasDerivAt (fun x : ℝ => c * x ^ 2)
          (c * (2 * (0 : ℝ) ^ (2 - 1) * 1)) 0 := by
        simpa only [id_eq] using HasDerivAt.const_mul c hsq
      have hexp := hinner.exp
      convert hexp using 1 <;> norm_num
    have hlin : HasDerivAt (fun t : ℝ => (2 * c) * t) (2 * c) 0 := by
      have h := HasDerivAt.const_mul (2 * c) (hasDerivAt_id 0)
      simpa only [id_eq, mul_one] using h
    have hmul := he.mul hlin
    have hmul' : HasDerivAt
        ((fun t : ℝ => Real.exp (c * t ^ 2)) * (fun t : ℝ => (2 * c) * t))
        (2 * c) 0 := by
      simpa [Real.exp_zero, mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      deriv (deriv (fun t : ℝ => Real.exp (c * t ^ 2))) 0 =
          deriv ((fun t : ℝ => Real.exp (c * t ^ 2)) *
            (fun t : ℝ => (2 * c) * t)) 0 := by
            rw [hderiv']
      _ = 2 * c := hmul'.deriv
  have hquot :
      (fun t : ℝ => Real.exp (-t ^ 2) / Real.exp (-2 * t ^ 2)) =
        (fun t : ℝ => Real.exp (t ^ 2)) := by
    funext t
    rw [← Real.exp_sub]
    congr 1
    ring
  have hneg :
      (fun t : ℝ => Real.exp (-t ^ 2)) =
        (fun t : ℝ => Real.exp ((-1 : ℝ) * t ^ 2)) := by
    funext t
    congr 1
    ring
  have hpos :
      (fun t : ℝ => Real.exp (t ^ 2)) =
        (fun t : ℝ => Real.exp ((1 : ℝ) * t ^ 2)) := by
    funext t
    congr 1
    ring
  constructor
  · rw [hneg, hsecond (-1)]
    norm_num
  constructor
  · rw [hsecond (-2)]
    norm_num
  · rw [hquot, hpos, hsecond 1]
    norm_num

end MathlibPlus.Analysis
