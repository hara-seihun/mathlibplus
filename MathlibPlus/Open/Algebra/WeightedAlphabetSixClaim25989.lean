import MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25975
import MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978

namespace MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25989

open MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25975

namespace Sixfold

abbrev Index := MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.Index
abbrev Composition (m N : ℕ) :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.Composition m N

/-- The pair member coupled to a degree-six middle candidate by the same
cubic pair correction used through degree five. -/
def degreeSixCoupledPair (N : ℕ) (k : Index N → ℚ)
    (p₀ p₁ p₂ p₃ : ℚ) : Index N → ℚ :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.coupledPairCandidate
    N k p₀ p₁ p₂ p₃

/-- The singleton member determined by the displayed coupled pair and middle
candidate, with the same affine freedom as the complete six-factor formula. -/
def degreeSixCoupledSingleton (N : ℕ) (k : Index N → ℚ)
    (p₀ p₁ p₂ p₃ A B : ℚ) : Index N → ℚ :=
  fun t =>
    A + B * (t.1 : ℚ) -
      3 * degreeSixCoupledPair N k p₀ p₁ p₂ p₃ t -
      degreeSixCoupledPair N k p₀ p₁ p₂ p₃
        (MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.reflectIndex N t) -
      6 * k t

/-- Claim 25989: the degree-five coupled family is valid, but a nonzero cubic
term in `t(N-t)` gives a nonvanishing fixed-total sixfold test and cannot be
absorbed by the displayed coupled pair/singleton family. -/
def claim25989 : Prop :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25975.claim25975 ∧
    ∀ (N : ℕ), 6 ≤ N →
      ∀ (d₀ d₁ d₂ d₃ : ℚ), d₃ ≠ 0 →
        let k :=
          MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.cubicMiddleCandidate
            N d₀ d₁ d₂ d₃
        (∃ μ : Composition 6 N,
            MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.mixedDifference k μ ≠ 0) ∧
          ∀ (p₀ p₁ p₂ p₃ A B : ℚ),
            ¬ MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978.sixFactorAnnihilator
                N (degreeSixCoupledSingleton N k p₀ p₁ p₂ p₃ A B)
                  (degreeSixCoupledPair N k p₀ p₁ p₂ p₃) k

end Sixfold

end MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25989
