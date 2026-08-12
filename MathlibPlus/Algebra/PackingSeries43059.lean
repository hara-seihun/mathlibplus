import Mathlib.Algebra.Field.Basic

namespace MathlibPlus.Algebra

/-- Claim 43059's outsider-difference consequence: once the two displayed
factorizations are assumed, the hypersurface `H_d = H_c` forces both repeated
normalization differences to vanish.  The source does not specify a
realizability predicate for the quotient `C`, so none is added here. -/
theorem outsiderDifferenceForcesRepeatedDifferences_43059
    {K : Type*} [Field K]
    (Ha Hb Hc Hd C lambda : K)
    (ha : Ha - Hc = (Hd - Hc) * C)
    (hb : Hb - Hc =
      (Hd - Hc) * (lambda * C / (1 + (lambda - 1) * C))) :
    Hd = Hc → Ha = Hc ∧ Hb = Hc := by
  intro h
  have ha0 : Ha - Hc = 0 := by
    simpa [h] using ha
  have hb0 : Hb - Hc = 0 := by
    simpa [h] using hb
  exact ⟨sub_eq_zero.mp ha0, sub_eq_zero.mp hb0⟩

end MathlibPlus.Algebra
