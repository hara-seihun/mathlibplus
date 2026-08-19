import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0754Claim29532

noncomputable section

private noncomputable def realPolynomial (Q : Polynomial ℤ) : Polynomial ℝ :=
  Q.map (algebraMap ℤ ℝ)

private noncomputable def oneExteriorRootData
    (Q : Polynomial ℤ) (δ : ℝ) (α : Fin 27 → ℝ) : Prop :=
  Q.Monic ∧
    Q.natDegree = 28 ∧
    0 < δ ∧
    δ < (27 : ℝ) / 1000 ∧
    (∀ i : Fin 27, 0 < α i ∧ α i < 4) ∧
    realPolynomial Q =
      (Polynomial.X - Polynomial.C (4 + δ)) *
        ∏ i : Fin 27, (Polynomial.X - Polynomial.C (α i))

/-- Claim 29532: the exact endpoint factorization and its positive-integer
log-gap consequence for the degree-28 one-exterior root data. -/
def endpointProductIdentity_claim29532 : Prop :=
  ∀ (Q : Polynomial ℤ) (δ : ℝ) (α : Fin 27 → ℝ),
    oneExteriorRootData Q δ α →
      -(realPolynomial Q).eval (4 : ℝ) =
          δ * ∏ i : Fin 27, (4 - α i) ∧
        ((∃ n : ℕ, 0 < n ∧
            -(realPolynomial Q).eval (4 : ℝ) = (n : ℝ)) →
          1 ≤ -(realPolynomial Q).eval (4 : ℝ) ∧
            ∑ i : Fin 27, Real.log (4 - α i) ≥ -Real.log δ)

end

end MathlibPlus.Open.ResearchFormalization.R0754Claim29532
