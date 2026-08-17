import MathlibPlus.Open.NewResearch2.RationalHankel15112

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.RationalHankel15111

noncomputable section

open RationalHankel15112

/-- Claim 15111: normalized Hermite evaluation on the degree-bounded
polynomial space is represented by the displayed confluent matrix, and that
matrix is invertible as a map between its coefficient and jet carriers. -/
def claim_15111 : Prop :=
  ∀ (J : ℕ) (zeta : Fin J → ℂ) (mu : Fin J → ℕ)
    (S : Polynomial ℂ),
    (∀ u v : Fin J, u ≠ v → zeta u ≠ zeta v) →
      (∀ u : Fin J, 0 < mu u) →
        S = ∏ u : Fin J,
          (Polynomial.X - Polynomial.C (zeta u)) ^ mu u →
          let m := ∑ u : Fin J, mu u
          let Phi := confluentHermiteMatrix zeta mu
          (∀ R : Polynomial ℂ,
              (R = 0 ∨ R.natDegree < m) →
                normalizedHermiteJets zeta mu R =
                  Phi.mulVec (polynomialCoefficientVector m R)) ∧
            Function.Bijective Phi.mulVec

end

end MathlibPlus.Open.NewResearch2.RationalHankel15111
