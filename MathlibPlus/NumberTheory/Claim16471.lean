import Mathlib.Analysis.Polynomial.MahlerMeasure

namespace MathlibPlus.NumberTheory

/-- Claim 16471: Mahler measure is the leading-coefficient factor times the
product of the max-one root norms, with roots counted with multiplicity. -/
theorem mahlerMeasure_factorization_claim16471 (P : Polynomial ℂ) :
    P.mahlerMeasure =
      ‖P.leadingCoeff‖ * (P.roots.map (fun α => max 1 ‖α‖)).prod := by
  exact Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots P

end MathlibPlus.NumberTheory
