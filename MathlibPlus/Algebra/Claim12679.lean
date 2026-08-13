import Mathlib

namespace MathlibPlus.Algebra.Claim12679

/-- In the residue field, the relation `p * t - 1` is the unit `-1`, so its
principal ideal is the whole polynomial ring.  This is the exact ordinary
Tensor-vanishing core of claim 12679. -/
theorem residuePolynomialIdeal_top_claim12679
    (p : ℕ) [Fact p.Prime] :
    Ideal.span ({(p : Polynomial (ZMod p)) * Polynomial.X - 1} :
      Set (Polynomial (ZMod p))) = ⊤ := by
  have hpoly : (p : Polynomial (ZMod p)) * Polynomial.X - 1 =
      (-1 : Polynomial (ZMod p)) := by
    simp
  rw [hpoly]
  exact Ideal.span_singleton_eq_top.mpr
    (isUnit_neg_one : IsUnit (-1 : Polynomial (ZMod p)))

end MathlibPlus.Algebra.Claim12679
