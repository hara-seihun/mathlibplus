import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim23447

/-!
The ambient algebra `ℚ[z, x₁, x₂, …]` is represented as
`Polynomial (MvPolynomial ℕ ℚ)`: the outer polynomial variable is `z`, and
`MvPolynomial ℕ ℚ` supplies the variables `x₁, x₂, …` (with index `i`
standing for `x_(i+1)`).  The displayed weights are therefore the outer
polynomial degree-one weight for `z` and the index-plus-one weight for `x`.
-/

/-- Every polynomial has a unique finite expansion in powers of the distinguished
outer variable, with coefficients in the polynomial algebra in the remaining
variables. -/
theorem uniqueZExpansion_claim23447
    (P : Polynomial (MvPolynomial ℕ ℚ)) :
    ∃! c : ℕ → MvPolynomial ℕ ℚ,
      (∀ k, c k = P.coeff k) ∧
        P = ∑ k ∈ P.support, Polynomial.C (c k) * Polynomial.X ^ k := by
  refine ⟨fun k => P.coeff k, ?_, ?_⟩
  · constructor
    · intro k
      rfl
    · simpa using P.as_sum_support_C_mul_X_pow
  · intro c hc
    exact funext hc.1

end MathlibPlus.Algebra.Claim23447
