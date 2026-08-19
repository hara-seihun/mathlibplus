import MathlibPlus.Open.ResearchFormalization.R0099EulerCurrent

namespace MathlibPlus.Algebra.Claim17930

open MathlibPlus.Open.ResearchFormalization.R0099EulerCurrent

noncomputable section

/-- The coefficient of `H(z) D H(w) - D H(z) H(w)` is
`(b-a) h_a h_b`, with `D = z ∂_z`. -/
theorem eulerCurrent_coefficient_formula
    {R : Type*} [CommRing R]
    (H : PowerSeries R) (a b : ℕ) :
    (PowerSeries.coeff a) H * (PowerSeries.coeff b) (eulerOperator H) -
        (PowerSeries.coeff a) (eulerOperator H) * (PowerSeries.coeff b) H =
      ((b : R) - (a : R)) * (PowerSeries.coeff a) H *
        (PowerSeries.coeff b) H := by
  rw [eulerOperator]
  have hcoeff (n : ℕ) :
      (PowerSeries.coeff n) (PowerSeries.X * PowerSeries.derivative R H) =
        (PowerSeries.coeff n) H * (n : R) := by
    cases n with
    | zero =>
        simp [PowerSeries.coeff_derivative]
    | succ n =>
        rw [show PowerSeries.X = PowerSeries.X ^ 1 by simp]
        rw [PowerSeries.coeff_X_pow_mul']
        have hn : 1 + n ≠ 0 := by omega
        simp [hn, PowerSeries.coeff_derivative]
  rw [hcoeff a, hcoeff b]
  ring

end
end MathlibPlus.Algebra.Claim17930
