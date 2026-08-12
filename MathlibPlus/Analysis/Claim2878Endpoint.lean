import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Interval

namespace MathlibPlus.Analysis.Claim2878

/-!
# Exact Gaussian cell integral

Formalization of admitted claim 2878.  The packet does not specify the type of
`n`, so the formalization takes `n : ℝ` (and therefore covers integer cell
indices).  The endpoint-deficit identity is proved directly by the fundamental
theorem of calculus.

The pinned mathlib does not provide a `Real.erf` declaration.  The first display
is consequently stated with an explicit `erf` function and a bridge hypothesis
for its standard Gaussian-integral normalization; no convention is silently
invented.  For `c > 0`, the source's `c^(3/2)` is represented by the equal
positive expression `c * √c`.
-/

/-- The endpoint-deficit form of the exact Gaussian cell integral. -/
theorem endpointDeficit (c n : ℝ) (hc : c ≠ 0) :
    (∫ x in n..n + 1, x * (x - n) * Real.exp (-c * x ^ 2)) =
      (1 / (2 * c)) *
        ((∫ x in n..n + 1, Real.exp (-c * x ^ 2)) -
          Real.exp (-c * (n + 1) ^ 2)) := by
  let f : ℝ → ℝ :=
    (fun x : ℝ => x - n) * (fun x : ℝ => Real.exp (-c * x ^ 2))
  have hf : ∀ x : ℝ,
      HasDerivAt f
        (1 * Real.exp (-c * x ^ 2) +
          (x - n) * (Real.exp (-c * x ^ 2) * (-c * (2 * x)))) x := by
    intro x
    have hpoly : HasDerivAt (fun y : ℝ => -c * y ^ 2) (-c * (2 * x)) x := by
      simpa [id, pow_two] using ((hasDerivAt_id x).pow 2).const_mul (-c)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-c * y ^ 2))
        (Real.exp (-c * x ^ 2) * (-c * (2 * x))) x := by
      exact hpoly.exp
    have hlin : HasDerivAt (fun y : ℝ => y - n) 1 x := by
      simpa using (hasDerivAt_id x).sub_const n
    simpa [f, Pi.mul_apply] using hlin.mul hexp
  have hderiv : deriv f = fun x : ℝ =>
      1 * Real.exp (-c * x ^ 2) +
        (x - n) * (Real.exp (-c * x ^ 2) * (-c * (2 * x))) := by
    funext x
    exact (hf x).deriv
  have hfund := intervalIntegral.integral_deriv_eq_sub' f hderiv
      (fun x _ => (hf x).differentiableAt)
      (by fun_prop : ContinuousOn
        (fun x : ℝ => 1 * Real.exp (-c * x ^ 2) +
          (x - n) * (Real.exp (-c * x ^ 2) * (-c * (2 * x))))
        (Set.uIcc n (n + 1)))
  have hfund' :
      (∫ x in n..n + 1,
          (Real.exp (-c * x ^ 2) - 2 * c * x * (x - n) * Real.exp (-c * x ^ 2))) =
        Real.exp (-c * (n + 1) ^ 2) := by
    calc
      (∫ x in n..n + 1,
          (Real.exp (-c * x ^ 2) - 2 * c * x * (x - n) * Real.exp (-c * x ^ 2))) =
          ∫ x in n..n + 1,
            (1 * Real.exp (-c * x ^ 2) +
              (x - n) * (Real.exp (-c * x ^ 2) * (-c * (2 * x)))) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = f (n + 1) - f n := hfund
      _ = Real.exp (-c * (n + 1) ^ 2) := by simp [f]
  have h_exp_cont : Continuous (fun x : ℝ => Real.exp (-c * x ^ 2)) := by
    fun_prop
  have h_prod_cont : Continuous
      (fun x : ℝ => 2 * c * x * (x - n) * Real.exp (-c * x ^ 2)) := by
    fun_prop
  have hsplit :
      (∫ x in n..n + 1,
          (Real.exp (-c * x ^ 2) - 2 * c * x * (x - n) * Real.exp (-c * x ^ 2))) =
        (∫ x in n..n + 1, Real.exp (-c * x ^ 2)) -
          ∫ x in n..n + 1, 2 * c * x * (x - n) * Real.exp (-c * x ^ 2) := by
    rw [intervalIntegral.integral_sub]
    · exact h_exp_cont.intervalIntegrable n (n + 1)
    · exact h_prod_cont.intervalIntegrable n (n + 1)
  have hprod :
      (∫ x in n..n + 1, 2 * c * x * (x - n) * Real.exp (-c * x ^ 2)) =
        2 * c * (∫ x in n..n + 1, x * (x - n) * Real.exp (-c * x ^ 2)) := by
    rw [show (fun x : ℝ => 2 * c * x * (x - n) * Real.exp (-c * x ^ 2)) =
        (fun x => (2 * c) * (x * (x - n) * Real.exp (-c * x ^ 2))) by
          funext x; ring]
    rw [intervalIntegral.integral_const_mul]
  have htarget :
      2 * c * (∫ x in n..n + 1, x * (x - n) * Real.exp (-c * x ^ 2)) =
        (∫ x in n..n + 1, Real.exp (-c * x ^ 2)) -
          Real.exp (-c * (n + 1) ^ 2) := by
    linarith [hfund', hsplit, hprod]
  calc
    (∫ x in n..n + 1, x * (x - n) * Real.exp (-c * x ^ 2)) =
        (1 / (2 * c)) *
          (2 * c * (∫ x in n..n + 1, x * (x - n) * Real.exp (-c * x ^ 2))) := by
            field_simp
            apply intervalIntegral.integral_congr
            intro x hx
            dsimp
            rw [show (-(x ^ 2 * c) : ℝ) = -(c * x ^ 2) by ring]
    _ = (1 / (2 * c)) *
          ((∫ x in n..n + 1, Real.exp (-c * x ^ 2)) -
            Real.exp (-c * (n + 1) ^ 2)) := by rw [htarget]

end MathlibPlus.Analysis.Claim2878
