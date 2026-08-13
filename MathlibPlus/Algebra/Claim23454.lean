import Mathlib

namespace MathlibPlus.Algebra

open scoped BigOperators

/-- The exponent substitution `(a,b) ↦ (b,a+b)` is injective on the
monomials of `ℚ[z,x₁]`; equivalently, the specialization
`z^a x₁^b ↦ u^b v^(a+b)` is injective. -/
theorem specialization_injective_claim23454 :
    Function.Injective
      (AddMonoidAlgebra.mapDomain (R := ℚ)
        (fun m : Fin 2 →₀ ℕ =>
          Finsupp.single (0 : Fin 2) (m 1) +
            Finsupp.single (1 : Fin 2) (m 0 + m 1))) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro m n h
  have h1 : m 1 = n 1 := by
    simpa using congrArg (fun r : Fin 2 →₀ ℕ => r 0) h
  have hsum : m 0 + m 1 = n 0 + n 1 := by
    simpa using congrArg (fun r : Fin 2 →₀ ℕ => r 1) h
  have h0 : m 0 = n 0 := by
    omega
  apply Finsupp.ext
  intro i
  fin_cases i
  · simpa using h0
  · simpa using h1

end MathlibPlus.Algebra
