import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim6259

/-!
The source's `S₁(C)` is a nonzero element of its domain polynomial ring.  The
nonzero side condition is explicit here rather than being hidden in a carrier.
-/

/-- A zero product with a nonzero constant factor has zero residual constant. -/
theorem constantResidual_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {h₀ s : R} (hs : s ≠ 0) (h : h₀ * s = 0) : h₀ = 0 := by
  exact (mul_eq_zero.mp h).resolve_right hs

end MathlibPlus.Algebra.Claim6259

namespace MathlibPlus.Algebra.Claim2825

/-!
The series below are already written after the source substitution `z = -t`:
`E` is `E(-t)` and `F` is `F(-t)`.  Thus the displayed factor is
`1 - t/α`.  The inverse equations are kept as hypotheses so that the theorem
states the exact formal-power-series cancellation without inventing an
analytic convergence or residue API.
-/

/-- The reciprocal of the deflated series is the first-difference transform. -/
theorem reciprocal_first_difference
    {R : Type*} [Field R]
    (α : R) (hα : α ≠ 0)
    (E F H K : PowerSeries R)
    (hE : E = (1 - PowerSeries.C α⁻¹ * PowerSeries.X) * F)
    (hH : H * E = 1) (hK : K * F = 1) :
    K = (1 - PowerSeries.C α⁻¹ * PowerSeries.X) * H := by
  have hF : F ≠ 0 := by
    intro hF
    rw [hF, mul_zero] at hK
    simpa using hK
  apply mul_right_cancel₀ hF
  calc
    K * F = 1 := hK
    _ = H * E := hH.symm
    _ = H * ((1 - PowerSeries.C α⁻¹ * PowerSeries.X) * F) := by rw [hE]
    _ = ((1 - PowerSeries.C α⁻¹ * PowerSeries.X) * H) * F := by ring

/-- Coefficients of the reciprocal first-difference transform. -/
theorem reciprocal_first_difference_coeff
    {R : Type*} [Field R]
    (α : R) (H : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n ((1 - PowerSeries.C α⁻¹ * PowerSeries.X) * H) =
      PowerSeries.coeff n H -
        α⁻¹ * (if n = 0 then 0 else PowerSeries.coeff (n - 1) H) := by
  have hexpand :
      (1 - PowerSeries.C α⁻¹ * PowerSeries.X) * H =
        H - PowerSeries.C α⁻¹ * (PowerSeries.X * H) := by ring
  rw [hexpand]
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_succ_X_mul]

/-- The coefficient recurrence follows from the reciprocal identities. -/
theorem reciprocal_first_difference_coeff_of_relation
    {R : Type*} [Field R]
    (α : R) (hα : α ≠ 0)
    (E F H K : PowerSeries R)
    (hE : E = (1 - PowerSeries.C α⁻¹ * PowerSeries.X) * F)
    (hH : H * E = 1) (hK : K * F = 1) (n : ℕ) :
    PowerSeries.coeff n K =
      PowerSeries.coeff n H -
        α⁻¹ * (if n = 0 then 0 else PowerSeries.coeff (n - 1) H) := by
  rw [reciprocal_first_difference α hα E F H K hE hH hK]
  exact reciprocal_first_difference_coeff α H n

end MathlibPlus.Algebra.Claim2825
