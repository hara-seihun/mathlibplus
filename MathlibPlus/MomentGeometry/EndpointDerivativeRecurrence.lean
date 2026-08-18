import Mathlib

/-!
# Endpoint exponential-polynomial derivative recurrence

Exact differentiation recurrence extracted from the admitted endpoint-packet
claim.  The parameters remain explicit so the two TP4 packets are included by
specialization.
-/

namespace MathlibPlus.MomentGeometry

noncomputable section

/-- Polynomial sequence governing repeated derivatives of
`exp (αt - q exp (st))`. -/
def endpointPolynomial (alpha s : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | j + 1 =>
      (Polynomial.C alpha - Polynomial.C s * Polynomial.X) *
          endpointPolynomial alpha s j +
        Polynomial.C s * Polynomial.X *
          (endpointPolynomial alpha s j).derivative

/-- Repeated differentiation of the endpoint packet is evaluation of
`endpointPolynomial` at `q exp(st)`, times the original packet. -/
theorem endpointDerivativeRecurrence
    (alpha s q t : ℝ) (j : ℕ) :
    (deriv^[j])
        (fun u : ℝ => Real.exp (alpha * u - q * Real.exp (s * u))) t =
      (endpointPolynomial alpha s j).eval (q * Real.exp (s * t)) *
        Real.exp (alpha * t - q * Real.exp (s * t)) := by
  induction j generalizing t with
  | zero => simp [endpointPolynomial]
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hfun :
          (deriv^[j])
              (fun u : ℝ => Real.exp (alpha * u - q * Real.exp (s * u))) =
            fun u : ℝ =>
              (endpointPolynomial alpha s j).eval (q * Real.exp (s * u)) *
                Real.exp (alpha * u - q * Real.exp (s * u)) := by
        funext u
        exact ih u
      rw [hfun]
      let y : ℝ → ℝ := fun u => q * Real.exp (s * u)
      let f : ℝ → ℝ := fun u => Real.exp (alpha * u - q * Real.exp (s * u))
      have hsu : HasDerivAt (fun u : ℝ => s * u) s t := by
        convert! (hasDerivAt_const t s).mul (hasDerivAt_id t) using 1
        all_goals ring
      have hsexp : HasDerivAt (fun u : ℝ => Real.exp (s * u))
          (s * Real.exp (s * t)) t := by
        simpa only [mul_comm] using hsu.exp
      have hy : HasDerivAt y (s * y t) t := by
        dsimp [y]
        convert! hsexp.const_mul q using 1
        all_goals ring
      have halpha : HasDerivAt (fun u : ℝ => alpha * u) alpha t := by
        convert! (hasDerivAt_const t alpha).mul (hasDerivAt_id t) using 1
        all_goals ring
      have hqexp : HasDerivAt (fun u : ℝ => q * Real.exp (s * u))
          (q * s * Real.exp (s * t)) t := by
        convert! hsexp.const_mul q using 1
        all_goals ring
      have hexponent : HasDerivAt
          (fun u : ℝ => alpha * u - q * Real.exp (s * u))
          (alpha - q * s * Real.exp (s * t)) t := by
        convert! halpha.sub hqexp using 1
      have hf : HasDerivAt f ((alpha - s * y t) * f t) t := by
        dsimp [f, y]
        convert! hexponent.exp using 1
        all_goals ring
      have hp : HasDerivAt
          (fun u => (endpointPolynomial alpha s j).eval (y u))
          ((endpointPolynomial alpha s j).derivative.eval (y t) * (s * y t)) t := by
        convert! ((endpointPolynomial alpha s j).hasDerivAt (y t)).comp t hy using 1
      have hprod : HasDerivAt
          (fun u => (endpointPolynomial alpha s j).eval (y u) * f u)
          ((endpointPolynomial alpha s j).derivative.eval (y t) * (s * y t) * f t +
            (endpointPolynomial alpha s j).eval (y t) *
              ((alpha - s * y t) * f t)) t := by
        convert! hp.mul hf using 1
      change deriv (fun u => (endpointPolynomial alpha s j).eval (y u) * f u) t = _
      rw [hprod.deriv]
      dsimp [y, f] at *
      simp only [endpointPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      ring

end

end MathlibPlus.MomentGeometry
