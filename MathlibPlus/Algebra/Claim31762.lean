import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- The only units in a finite polynomial presentation of the strict
lower-marker ring are nonzero rational constants. -/
theorem strictLowerMarkerUnits31762 (J : ℕ)
    (f : MvPolynomial (Fin (J - 1)) ℚ) (hf : IsUnit f) :
    ∃ q : ℚ, q ≠ 0 ∧ f = MvPolynomial.C q := by
  rcases (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hf) with ⟨q, hq, hqf⟩
  refine ⟨q, (isUnit_iff_ne_zero.mp hq), hqf⟩

end MathlibPlus.Algebra
