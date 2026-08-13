import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- A finite coefficientwise relation is preserved by every finite linear
profile functional. -/
theorem claim49921_additive_profile_linearity
    {R Λ I : Type*} [CommRing R] [Fintype Λ] [Fintype I]
    (f : Λ → R) (c : I → R) (U : I → Λ → R)
    (hcoeff : ∀ (part : Λ), ∑ i, c i * U i part = 0) :
    ∑ i, c i * (∑ part, U i part * f part) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro part hpart
  calc
    (∑ i, c i * (U i part * f part)) =
        (∑ i, c i * U i part) * f part := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [hcoeff part, zero_mul]

end MathlibPlus.Algebra
