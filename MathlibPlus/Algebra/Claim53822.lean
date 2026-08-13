import Mathlib

open Polynomial

namespace MathlibPlus.Algebra.Claim53822

/-- The shifted endpoint-rooted path quotient has the displayed factorization. -/
theorem shiftedPathQuotient_factorization_claim53822 :
    (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℚ) =
      (1 + Polynomial.X) * (1 + Polynomial.X ^ 2) := by
  ring

/-- The displayed shifted quotient is not irreducible over `ℚ`. -/
theorem shiftedPathQuotient_not_irreducible_claim53822 :
    ¬ Irreducible (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℚ) := by
  intro h
  have hfac :
      (1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℚ) =
        (1 + Polynomial.X) * (1 + Polynomial.X ^ 2) :=
    shiftedPathQuotient_factorization_claim53822
  rcases h.isUnit_or_isUnit hfac with hlin | hquad
  · have hdeg : (1 : Polynomial ℚ).degree < (Polynomial.X : Polynomial ℚ).degree := by
      simp
    have hpos : 0 < (1 + Polynomial.X : Polynomial ℚ).degree := by
      rw [Polynomial.degree_add_eq_right_of_degree_lt hdeg]
      simp
    exact (Polynomial.not_isUnit_of_degree_pos (1 + Polynomial.X) hpos) hlin
  · have hdeg : (1 : Polynomial ℚ).degree < ((Polynomial.X : Polynomial ℚ) ^ 2).degree := by
      simp
    have hpos : 0 < (1 + Polynomial.X ^ 2 : Polynomial ℚ).degree := by
      rw [Polynomial.degree_add_eq_right_of_degree_lt hdeg]
      simp
    exact (Polynomial.not_isUnit_of_degree_pos (1 + Polynomial.X ^ 2) hpos) hquad

end MathlibPlus.Algebra.Claim53822
