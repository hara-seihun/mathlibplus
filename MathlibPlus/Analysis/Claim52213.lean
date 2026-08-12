import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim52213

open scoped BigOperators Pointwise ComplexConjugate

noncomputable section

/-- Claim 52213 under the standard finite additive-character convention: translating
an index set gives the character phase, and reflection gives complex conjugation. -/
theorem translation_and_reflection_identities
    {D : Type*} [AddCommGroup D] [Fintype D] [DecidableEq D]
    (A : Finset D) (u : D) (ψ : AddChar D ℂ) :
    (∑ x ∈ A.image (fun x => x + u), ψ x =
      ψ u * (∑ x ∈ A, ψ x)) ∧
    (∑ x ∈ A.image (fun x => -x), ψ x =
      conj (∑ x ∈ A, ψ x)) := by
  classical
  constructor
  · rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [AddChar.map_add_eq_mul]
      rw [mul_comm]
    · intro x hx y hy hxy
      exact add_right_cancel hxy
  · rw [Finset.sum_image]
    · rw [map_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [AddChar.map_neg_eq_conj]
    · intro x hx y hy hxy
      exact neg_injective hxy

end
end MathlibPlus.Analysis.Claim52213
