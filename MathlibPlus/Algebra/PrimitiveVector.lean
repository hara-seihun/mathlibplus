import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Algebra.PrimitiveVector

/-- Claim 27653: a rational scalar taking a primitive integral vector to an
integral vector is itself integral.  The displayed Bézout relation is the
coordinate form of primitivity used here. -/
theorem primitiveVector_scalar_integrality_claim27653
    {ι : Type*} [Fintype ι]
    (d : ι → ℤ) (c : ℚ)
    (hprimitive : ∃ a : ι → ℤ, ∑ i, a i * d i = 1)
    (hintegral : ∀ i, ∃ z : ℤ, c * (d i : ℚ) = z) :
    ∃ z : ℤ, c = z := by
  rcases hprimitive with ⟨a, ha⟩
  choose z hz using hintegral
  refine ⟨∑ i, a i * z i, ?_⟩
  calc
    c = c * 1 := by ring
    _ = c * (∑ i, (a i : ℚ) * (d i : ℚ)) := by
      have haQ : (∑ i, (a i : ℚ) * (d i : ℚ)) = 1 := by
        norm_cast
      rw [haQ]
    _ = ∑ i, (a i : ℚ) * (c * (d i : ℚ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, (a i : ℚ) * (z i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hz i]
    _ = (∑ i, a i * z i : ℤ) := by
      norm_cast

end MathlibPlus.Algebra.PrimitiveVector
