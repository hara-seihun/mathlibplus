import Mathlib

/-!
# Formal coefficient differences (claim 4187)

The packet does not specify whether its "coefficients" are ordinary power-series
coefficients or exponential/Taylor coefficients, nor does it specify a scalar
ring.  This module makes the convention explicit: `F` is a rational formal power
series, `G = exp * F`, and `S n = n! * [X^n] G`.  Thus `S` is the coefficient
sequence in the exponential basis.  The asserted derivative and second-derivative
relations then hold formally, without an analytic convergence assumption.
-/

namespace MathlibPlus.Algebra.Claim4187

/-- With exponential/Taylor coefficient normalization, differentiation of `F`
becomes first forward difference of the coefficients of `exp * F`, and the
second derivative becomes the second forward difference. -/
theorem forwardDifferenceDerivativeCoefficients (F : PowerSeries ℚ) (n : ℕ) :
    let G := PowerSeries.exp ℚ * F
    let S : ℕ → ℚ := fun k => (k.factorial : ℚ) * PowerSeries.coeff k G
    let d := PowerSeries.derivative ℚ
    ((n.factorial : ℚ) * PowerSeries.coeff n
        (PowerSeries.exp ℚ * d F) = S (n + 1) - S n) ∧
      ((n.factorial : ℚ) * PowerSeries.coeff n
          (PowerSeries.exp ℚ * d (d F)) =
        S (n + 2) - 2 * S (n + 1) + S n) := by
  dsimp
  let d := PowerSeries.derivative ℚ
  let E := PowerSeries.exp ℚ
  let G := E * F
  have hG : d G = G + E * d F := by
    dsimp [G, E, d]
    rw [Derivation.leibniz, PowerSeries.derivative_exp]
    simp [smul_eq_mul, mul_comm, add_comm]
  have hfirst : E * d F = d G - G := by
    rw [hG]
    ring
  have hEdF : d (E * d F) = E * d F + E * d (d F) := by
    dsimp [E, d]
    rw [Derivation.leibniz, PowerSeries.derivative_exp]
    simp [smul_eq_mul, mul_comm, add_comm]
  have hsecond : E * d (d F) = d (d G) - d G - d G + G := by
    have hdiff := congrArg d hfirst
    rw [hEdF] at hdiff
    rw [map_sub] at hdiff
    calc
      E * d (d F) = d (d G) - d G - E * d F := by
        linear_combination hdiff
      _ = d (d G) - d G - d G + G := by rw [hfirst]; abel
  constructor
  · rw [hfirst]
    dsimp [G, E]
    simp only [map_sub]
    rw [PowerSeries.coeff_derivative]
    rw [Nat.factorial_succ]
    push_cast
    ring
  · rw [hsecond]
    dsimp [G, E]
    simp only [map_sub, map_add]
    rw [PowerSeries.coeff_derivative]
    rw [PowerSeries.coeff_derivative]
    rw [PowerSeries.coeff_derivative]
    rw [show n + 1 + 1 = n + 2 by omega, Nat.factorial_succ]
    rw [Nat.factorial_succ]
    push_cast
    ring

end MathlibPlus.Algebra.Claim4187
