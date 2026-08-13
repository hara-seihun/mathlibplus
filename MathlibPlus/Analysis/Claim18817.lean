import Mathlib

namespace MathlibPlus.Analysis.Claim18817

theorem compensated_jump_correlation_claim18817
    {α : Type*} [Fintype α] (e : α ≃ α) (f : α → ℂ) :
    (∑ x, Complex.normSq (f (e x) - f x)) -
        2 * ∑ x, Complex.normSq (f x) =
      -2 * (∑ x, (f (e x) * (starRingEnd ℂ) (f x))).re := by
  simp_rw [Complex.normSq_sub]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hnorm : (∑ x, Complex.normSq (f (e x))) =
      ∑ x, Complex.normSq (f x) := by
    exact Equiv.sum_comp e (fun x => Complex.normSq (f x))
  rw [hnorm]
  simp only [Complex.re_sum]
  rw [← Finset.mul_sum]
  ring

end MathlibPlus.Analysis.Claim18817
