import Mathlib

namespace MathlibPlus.Open.NumberTheory.AdmittedK0149

open scoped BigOperators LaurentPolynomial

/-- Claim 9180: a monic integral polynomial with all roots in [-2,2] has a
cyclotomic reciprocal lift.  The reciprocal expression is recorded in the
Laurent-polynomial carrier, so it is not replaced by an unrelated polynomial. -/
def claim9180 : Prop :=
  ∀ C : Polynomial ℤ,
    C.Monic →
      (∀ z : ℂ,
        Polynomial.IsRoot (C.map (Int.castRingHom ℂ)) z →
          z.im = 0 ∧ (-2 : ℝ) ≤ z.re ∧ z.re ≤ 2) →
        ∃ L : Polynomial ℤ,
          L.Monic ∧
            Polynomial.toLaurent L =
              LaurentPolynomial.T (C.natDegree : ℤ) *
                Polynomial.eval₂ LaurentPolynomial.C
                  (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) C ∧
            (∀ z : ℂ,
              Polynomial.IsRoot (L.map (Int.castRingHom ℂ)) z →
                ‖z‖ = 1) ∧
              (∃ e : ℕ →₀ ℕ,
                L =
                  e.support.prod (fun k =>
                    (Polynomial.cyclotomic k ℤ) ^ (e k))) ∧
                (L.map (Int.castRingHom ℂ)).mahlerMeasure = 1

end MathlibPlus.Open.NumberTheory.AdmittedK0149
