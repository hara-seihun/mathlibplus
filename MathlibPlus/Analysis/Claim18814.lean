import Mathlib

namespace MathlibPlus.Analysis.Claim18814

/-- The long-jump energy identity after the geometric support argument has
established disjointness of the original and shifted supports. -/
theorem disjoint_support_energy_claim18814
    {α : Type*} [Fintype α] (e : α ≃ α) (f : α → ℂ)
    (hdisjoint : ∀ x, f (e x) = 0 ∨ f x = 0) :
    ∑ x, Complex.normSq (f (e x) - f x) =
      2 * ∑ x, Complex.normSq (f x) := by
  simp_rw [Complex.normSq_sub]
  have hnorm : (∑ x, Complex.normSq (f (e x))) =
      ∑ x, Complex.normSq (f x) := by
    exact Equiv.sum_comp e (fun x => Complex.normSq (f x))
  have hcross : (∑ x, (f (e x) * (starRingEnd ℂ) (f x)).re) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rcases hdisjoint x with hzero | hzero
    · simp [hzero]
    · simp [hzero]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hnorm]
  rw [← Finset.mul_sum]
  rw [hcross]
  ring

end MathlibPlus.Analysis.Claim18814
