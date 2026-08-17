import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.EndpointMomentBoundsR0754Claim29533

noncomputable section

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

private def quadraticMajorant (a b γ : ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → y < 4 →
    Real.log y ≤ a + b * y - γ * y ^ 2

private def criticalPointCheck (a b γ : ℝ) : Prop :=
  Real.log 4 ≤ a + b * 4 - γ * 4 ^ 2 ∧
    ∀ y : ℝ, 0 < y → y < 4 →
      2 * γ * y ^ 2 - b * y + 1 = 0 →
        Real.log y ≤ a + b * y - γ * y ^ 2

private def quadraticBound (a b γ S d : ℝ) : ℝ :=
  (27 * a + b * (112 - S + d) + Real.log d) / γ -
    448 + 8 * S + d ^ 2

/-- Claim 29533: a global positive-rational quadratic logarithm majorant
implies the displayed second-Newton-sum bound; the delta monotonicity and the
finite endpoint/critical-point test are stated independently of that
implication. -/
def quadraticLogMajorantSecondNewtonBound_claim29533 : Prop :=
  (∀ (a b γ : ℚ), 0 < b → 0 < γ →
    ∀ (Q : Polynomial ℝ) (δ : ℝ) (α : Fin 27 → ℝ),
      oneExteriorRootData Q δ α →
      quadraticMajorant (a : ℝ) (b : ℝ) (γ : ℝ) →
      let S := traceSum δ α
      let p₂ := secondNewtonSum δ α
      p₂ ≤ quadraticBound (a : ℝ) (b : ℝ) (γ : ℝ) S δ) ∧
  (∀ (a b γ : ℚ), 0 < b → 0 < γ →
    ∀ (Q : Polynomial ℝ) (δ : ℝ) (α : Fin 27 → ℝ),
      oneExteriorRootData Q δ α →
      let S := traceSum δ α
      (∀ d : ℝ, 0 < d →
        HasDerivAt
          (quadraticBound (a : ℝ) (b : ℝ) (γ : ℝ) S)
          ((b : ℝ) / (γ : ℝ) + 1 / ((γ : ℝ) * d) + 2 * d) d ∧
          0 < (b : ℝ) / (γ : ℝ) + 1 / ((γ : ℝ) * d) + 2 * d) ∧
      (∀ d : ℝ, 0 < d → d < (27 : ℝ) / 1000 →
        quadraticBound (a : ℝ) (b : ℝ) (γ : ℝ) S d ≤
          quadraticBound (a : ℝ) (b : ℝ) (γ : ℝ) S ((27 : ℝ) / 1000))) ∧
  (∀ (a b γ : ℚ), 0 < b → 0 < γ →
    quadraticMajorant (a : ℝ) (b : ℝ) (γ : ℝ) ↔
      criticalPointCheck (a : ℝ) (b : ℝ) (γ : ℝ))

end

end MathlibPlus.Open.NumberTheory.EndpointMomentBoundsR0754Claim29533
