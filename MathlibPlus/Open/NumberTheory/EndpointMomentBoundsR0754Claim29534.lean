import Mathlib

namespace MathlibPlus.Open.NumberTheory.EndpointMomentBoundsR0754

noncomputable section
open scoped BigOperators

private def integerCoefficients (Q : Polynomial ℝ) : Prop :=
  ∀ n, ∃ z : ℤ, Q.coeff n = (z : ℝ)

private def oneExteriorPolynomial (δ : ℝ) (α : Fin 27 → ℝ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C (4 + δ)) *
    ∏ i : Fin 27, (Polynomial.X - Polynomial.C (α i))

private def oneExteriorRootData
    (Q : Polynomial ℝ) (δ : ℝ) (α : Fin 27 → ℝ) : Prop :=
  0 < δ ∧ δ < (27 : ℝ) / 1000 ∧
    (∀ i, 0 < α i ∧ α i < 4) ∧
    Q.Monic ∧ Q.natDegree = 28 ∧ integerCoefficients Q ∧
    Q = oneExteriorPolynomial δ α ∧
    -Q.eval (4 : ℝ) = δ * ∏ i : Fin 27, (4 - α i) ∧
    0 < -Q.eval (4 : ℝ) ∧
    ∃ n : ℤ, -Q.eval (4 : ℝ) = (n : ℝ)

private def traceSum (δ : ℝ) (α : Fin 27 → ℝ) : ℝ :=
  (4 + δ) + ∑ i : Fin 27, α i

private def secondNewtonSum (δ : ℝ) (α : Fin 27 → ℝ) : ℝ :=
  (4 + δ) ^ 2 + ∑ i : Fin 27, (α i) ^ 2

/-- Claim 29534: the eleven certified trace-dependent second-Newton-sum
ceilings for the degree-56 one-exterior carrier. -/
def certifiedTraceSecondNewtonCeilings_claim29534 : Prop :=
  ∀ (Q : Polynomial ℝ) (δ : ℝ) (α : Fin 27 → ℝ)
    (S p₂ : ℤ),
    oneExteriorRootData Q δ α →
    (S : ℝ) = traceSum δ α →
    (p₂ : ℝ) = secondNewtonSum δ α →
    51 ≤ S → S ≤ 61 →
    ((S = 51 ∧ p₂ ≤ 191) ∨
      (S = 52 ∧ p₂ ≤ 194) ∨
      (S = 53 ∧ p₂ ≤ 196) ∨
      (S = 54 ∧ p₂ ≤ 199) ∨
      (S = 55 ∧ p₂ ≤ 201) ∨
      (S = 56 ∧ p₂ ≤ 204) ∨
      (S = 57 ∧ p₂ ≤ 206) ∨
      (S = 58 ∧ p₂ ≤ 209) ∨
      (S = 59 ∧ p₂ ≤ 211) ∨
      (S = 60 ∧ p₂ ≤ 213) ∨
      (S = 61 ∧ p₂ ≤ 215))

end
end MathlibPlus.Open.NumberTheory.EndpointMomentBoundsR0754
