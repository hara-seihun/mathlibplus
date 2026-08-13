import Mathlib

namespace MathlibPlus.Algebra.Claim28974

/-- Claim 28974: a rational multiple of a primitive integral vector is integral
whenever all of its coordinates are integral. -/
theorem rational_parameter_of_primitive_integral_point
    {ι : Type*} [Fintype ι]
    (D a : ι → ℤ) (c : ℚ)
    (hprimitive : ∑ i, a i * D i = 1)
    (hintegral : ∀ i, ∃ z : ℤ, (z : ℚ) = c * (D i : ℚ)) :
    ∃ z : ℤ, (z : ℚ) = c := by
  classical
  let zcoord : ι → ℤ := fun i => Classical.choose (hintegral i)
  have hzcoord : ∀ i, (zcoord i : ℚ) = c * (D i : ℚ) := by
    intro i
    exact Classical.choose_spec (hintegral i)
  refine ⟨∑ i, a i * zcoord i, ?_⟩
  calc
    ((∑ i, a i * zcoord i : ℤ) : ℚ) =
        ∑ i, (a i : ℚ) * (zcoord i : ℚ) := by norm_cast
    _ = ∑ i, (a i : ℚ) * (c * (D i : ℚ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hzcoord i]
    _ = c * ∑ i, (a i : ℚ) * (D i : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c := by
      rw [show (∑ i, (a i : ℚ) * (D i : ℚ)) = (1 : ℚ) by
        exact_mod_cast hprimitive]
      ring

end MathlibPlus.Algebra.Claim28974
