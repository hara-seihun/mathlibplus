import Mathlib.Algebra.MvPolynomial.Nilpotent

namespace MathlibPlus.Algebra

/-!
Formalization of admitted claim 41526.  For `J ≥ 2`, the displayed ring
`ℚ[t,c₂,…,c_(J-1)]` is represented, up to a relabelling of its finite
variables, by `MvPolynomial (Fin (J - 1)) ℚ`.  The units theorem is independent
of those variable labels, so the declaration states exactly that its units are
nonzero rational constants.
-/

/-- The only units in the finite strict lower-marker polynomial ring are the
nonzero rational constants. -/
theorem strictLowerMarker_units_claim41526
    {J : ℕ} (_hJ : 2 ≤ J) (P : MvPolynomial (Fin (J - 1)) ℚ) :
    IsUnit P ↔ ∃ q : ℚ, q ≠ 0 ∧ P = MvPolynomial.C q := by
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  simp only [isUnit_iff_ne_zero]

end MathlibPlus.Algebra
