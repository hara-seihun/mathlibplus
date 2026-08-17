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

private def gapFirstMoment (α : Fin 27 → ℝ) : ℝ :=
  ∑ i : Fin 27, (4 - α i)

private def gapSecondMoment (α : Fin 27 → ℝ) : ℝ :=
  ∑ i : Fin 27, (4 - α i) ^ 2

/-- Claim 34998: Cauchy on the 27 interior gaps, the strictly increasing
positive-delta substituted lower bound, and its eleven strict integer floors. -/
def strictSecondNewtonInteriorGapBound_claim34998 : Prop :=
  ∀ (Q : Polynomial ℝ) (δ : ℝ) (α : Fin 27 → ℝ)
    (S p₂ : ℤ),
    oneExteriorRootData Q δ α →
    (S : ℝ) = traceSum δ α →
    (p₂ : ℝ) = secondNewtonSum δ α →
    51 ≤ S → S ≤ 61 →
    let Y : ℝ := gapFirstMoment α
    let Z : ℝ := gapSecondMoment α
    let L : ℝ → ℝ := fun d =>
      -448 + 8 * (S : ℝ) + d ^ 2 +
        (112 - (S : ℝ) + d) ^ 2 / 27
    ((Z = 448 - 8 * (S : ℝ) + (p₂ : ℝ) - δ ^ 2 ∧
      Y = 112 - (S : ℝ) + δ ∧
      Z ≥ Y ^ 2 / 27 ∧
      (p₂ : ℝ) ≥ L δ ∧
      (∀ d : ℝ, 0 < d →
        HasDerivAt L
          (2 * d + 2 * (112 - (S : ℝ) + d) / 27) d ∧
          0 < 2 * d + 2 * (112 - (S : ℝ) + d) / 27) ∧
      (p₂ : ℝ) >
        -448 + 8 * (S : ℝ) +
          (112 - (S : ℝ)) ^ 2 / 27 ∧
      ((S = 51 ∧ 98 ≤ p₂) ∨
        (S = 52 ∧ 102 ≤ p₂) ∨
        (S = 53 ∧ 105 ≤ p₂) ∨
        (S = 54 ∧ 109 ≤ p₂) ∨
        (S = 55 ∧ 113 ≤ p₂) ∨
        (S = 56 ∧ 117 ≤ p₂) ∨
        (S = 57 ∧ 121 ≤ p₂) ∨
        (S = 58 ∧ 125 ≤ p₂) ∨
        (S = 59 ∧ 129 ≤ p₂) ∨
        (S = 60 ∧ 133 ≤ p₂) ∨
        (S = 61 ∧ 137 ≤ p₂))))

end
end MathlibPlus.Open.NumberTheory.EndpointMomentBoundsR0754
