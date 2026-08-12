import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra

/-- A linear filter preserves every finite signed parent relation.  The
coefficient-vector and parent-family interfaces are kept abstract because the
source statement does not define its tree/U-polynomial carriers. -/
theorem claim57508_linearFilterPreservesRelation
    {ι P V W : Type*} [Fintype ι]
    [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W]
    (parent : ι → P) (u : P → V) (L : V →ₗ[ℚ] W)
    (ε : ι → ℚ)
    (h : ∑ i, ε i • u (parent i) = 0) :
    ∑ i, ε i • L (u (parent i)) = 0 := by
  calc
    ∑ i, ε i • L (u (parent i)) =
        ∑ i, L (ε i • u (parent i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
    _ = L (∑ i, ε i • u (parent i)) := by
      rw [map_sum]
    _ = 0 := by rw [h, map_zero]

end MathlibPlus.LinearAlgebra
