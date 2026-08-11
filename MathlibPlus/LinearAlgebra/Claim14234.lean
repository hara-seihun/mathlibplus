import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra

/-- Claim 14234: a nonzero balanced packet on pairwise-distinct shifts has a
nonzero moment of order at least two. -/
theorem higherMoment_nonzero_claim14234
    {K : Type*} [Field K] {n : ℕ} (α c : Fin n → K)
    (hα : Function.Injective α) (hc : c ≠ 0)
    (h0 : ∑ j : Fin n, c j = 0)
    (h1 : ∑ j : Fin n, c j * α j = 0) :
    ∃ r : ℕ, 2 ≤ r ∧ ∑ j : Fin n, c j * α j ^ r ≠ 0 := by
  by_contra h
  push Not at h
  have hall : ∀ r : ℕ, ∑ j : Fin n, c j * α j ^ r = 0 := by
    intro r
    rcases lt_or_ge r 2 with hr | hr
    · interval_cases r
      · simpa using h0
      · simpa [pow_one] using h1
    · exact h r hr
  have hc0 : c = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hα (fun i => by
      simpa using hall (i : ℕ))
  exact hc hc0

end MathlibPlus.LinearAlgebra
