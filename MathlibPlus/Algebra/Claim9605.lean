import Mathlib

namespace MathlibPlus.Algebra.Claim9605

/-- Claim 9605.  We represent an even integer polynomial by invariance under
`z ↦ -z`; the displayed family is retained literally. -/
theorem gripfallCounterfeitFamily (m : ℕ) (_hm : 0 < m) :
    ((1 + Polynomial.X ^ (4 * m) : Polynomial ℤ).comp (-Polynomial.X)) =
      1 + Polynomial.X ^ (4 * m) := by
  rw [Polynomial.add_comp, Polynomial.one_comp, Polynomial.pow_comp,
    Polynomial.X_comp]
  rw [Even.neg_pow]
  exact ⟨2 * m, by omega⟩

end MathlibPlus.Algebra.Claim9605
