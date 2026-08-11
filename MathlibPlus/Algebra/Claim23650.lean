import Mathlib

namespace MathlibPlus.Algebra.Claim23650

open scoped BigOperators PowerSeries

/-- The degree-`d` component of the product of two formal completed
homogeneous series. -/
theorem completedComponentProduct_formula
    {R : Type*} [CommSemiring R] (f g : R⟦X⟧) (d : ℕ) :
    PowerSeries.coeff d (f * g) =
      ∑ i ∈ Finset.range (d + 1),
        PowerSeries.coeff i f * PowerSeries.coeff (d - i) g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

end MathlibPlus.Algebra.Claim23650
