import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim11352

/-!
The `O(q^3)` and `O(q^2)` terms in the source are expressed by the exact
coefficients that they determine.  The coefficient computation below does
not impose any condition on the undetermined higher coefficients.
-/

/-- The exterior jet has second coefficient `-48`, not the vacuum coefficient
`2`, from the displayed first coefficients of `Δ` and `E₁₄`. -/
theorem exteriorJetCoefficient (Δ E : PowerSeries ℚ)
    (hΔ0 : PowerSeries.coeff 0 Δ = 0)
    (hΔ1 : PowerSeries.coeff 1 Δ = 1)
    (hΔ2 : PowerSeries.coeff 2 Δ = -24)
    (hE0 : PowerSeries.coeff 0 E = 1)
    (hE1 : PowerSeries.coeff 1 E = -24) :
    PowerSeries.coeff 2 (Δ * E) = -48 ∧
      PowerSeries.coeff 2 (Δ * E) ≠ 2 := by
  have hcoeff : PowerSeries.coeff 2 (Δ * E) =
      PowerSeries.coeff 0 Δ * PowerSeries.coeff 2 E +
      PowerSeries.coeff 1 Δ * PowerSeries.coeff 1 E +
      PowerSeries.coeff 2 Δ * PowerSeries.coeff 0 E := by
    rw [PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => PowerSeries.coeff p.1 Δ * PowerSeries.coeff p.2 E) 2]
    norm_num [Finset.sum_range_succ]
  rw [hcoeff, hΔ0, hΔ1, hΔ2, hE0, hE1]
  norm_num

end MathlibPlus.Algebra.Claim11352
