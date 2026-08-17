import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.EndpointMomentBoundsR0754Claim34999

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

private def thirdNewtonSum (δ : ℝ) (α : Fin 27 → ℝ) : ℝ :=
  (4 + δ) ^ 3 + ∑ i : Fin 27, (α i) ^ 3

private def gap (α : Fin 27 → ℝ) (i : Fin 27) : ℝ :=
  4 - α i

private def firstGapMoment (α : Fin 27 → ℝ) : ℝ :=
  ∑ i : Fin 27, gap α i

private def secondGapMoment (α : Fin 27 → ℝ) : ℝ :=
  ∑ i : Fin 27, (gap α i) ^ 2

private def thirdGapMoment (α : Fin 27 → ℝ) : ℝ :=
  ∑ i : Fin 27, (gap α i) ^ 3

private def cubicSupportLowerBound
    (S p₂ r d : ℝ) : ℝ :=
  1792 - 48 * S + 12 * p₂ + d ^ 3 -
    ((4 + 2 * r) * (448 - 8 * S + p₂ - d ^ 2) -
      (8 * r + r ^ 2) * (112 - S + d) + 108 * r ^ 2)

private def optimizedLowerBound (S p₂ : ℝ) : ℝ :=
  -16 * S + 8 * p₂ + (4 * S - p₂) ^ 2 / (S - 4)

private def optimizedLowerBoundExpanded (S p₂ : ℝ) : ℝ :=
  (p₂ ^ 2 - 32 * p₂ + 64 * S) / (S - 4)

/-- Claim 34999: the support-polynomial family, its fixed-`r` derivative and
strict positive-delta increase, and the direct optimized strict third-moment
bound are all retained on the one-exterior root carrier. -/
def optimizedCubicSupportThirdNewtonBound_claim34999 : Prop :=
  ∀ (Q : Polynomial ℝ) (δ : ℝ) (α : Fin 27 → ℝ),
    oneExteriorRootData Q δ α →
    let S := traceSum δ α
    let p₂ := secondNewtonSum δ α
    let p₃ := thirdNewtonSum δ α
    let Y := firstGapMoment α
    let Z := secondGapMoment α
    let W := thirdGapMoment α
    let r₀ := (4 * S - p₂) / (S - 4)
    let target := optimizedLowerBound S p₂
    (Y = 112 - S + δ ∧
      Z = 448 - 8 * S + p₂ - δ ^ 2 ∧
      W = 1792 - 48 * S + 12 * p₂ - p₃ + δ ^ 3) ∧
    (∀ r : ℝ, 0 < r →
      0 ≤ ∑ i : Fin 27, (4 - gap α i) * (gap α i - r) ^ 2 ∧
      p₃ ≥ cubicSupportLowerBound S p₂ r δ) ∧
    (∀ r : ℝ, 0 < r →
      ∀ d : ℝ, 0 < d →
        HasDerivAt (cubicSupportLowerBound S p₂ r)
          (3 * d ^ 2 + 8 * r + r ^ 2 +
            2 * (4 + 2 * r) * d) d ∧
        0 < 3 * d ^ 2 + 8 * r + r ^ 2 +
          2 * (4 + 2 * r) * d) ∧
    0 < r₀ ∧
    cubicSupportLowerBound S p₂ r₀ δ >
      cubicSupportLowerBound S p₂ r₀ 0 ∧
    cubicSupportLowerBound S p₂ r₀ 0 = target ∧
    p₃ > target ∧
    target = optimizedLowerBoundExpanded S p₂

end

end MathlibPlus.Open.NumberTheory.EndpointMomentBoundsR0754Claim34999
