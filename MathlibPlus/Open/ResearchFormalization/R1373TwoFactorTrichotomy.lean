import MathlibPlus.Algebra.Claim38341
import MathlibPlus.Algebra.Claim38342

namespace MathlibPlus.Open.ResearchFormalization.R1373

noncomputable section

private def twoFactorDerivativeEquality
    {K : Type*} [Field K] [CharZero K]
    (A B C D : Polynomial K) : Prop :=
  let Dx : Derivation K (Polynomial (Polynomial K)) (Polynomial (Polynomial K)) :=
    PolynomialModule.equivPolynomialSelf.compDer
      (Polynomial.derivative'.mapCoeffs)
  Dx ((Polynomial.X + Polynomial.C A) * (Polynomial.X + Polynomial.C B)) =
    Dx ((Polynomial.X + Polynomial.C C) * (Polynomial.X + Polynomial.C D))

private def factorSum {K : Type*} [Semiring K]
    (A B : Polynomial K) : Polynomial K := A + B

private def factorDifference {K : Type*} [Ring K]
    (A B : Polynomial K) : Polynomial K := A - B

private def unorderedFactorPair {K : Type*} [Semiring K]
    (A B C D : Polynomial K) : Prop :=
  Multiset.cons A (Multiset.cons B 0) =
    Multiset.cons C (Multiset.cons D 0)

private def commonTwoFactorHypotheses
    {K : Type*} [Field K] [CharZero K]
    (m : ℕ) (A B C D : Polynomial K) : Prop :=
  A.Monic ∧ B.Monic ∧ C.Monic ∧ D.Monic ∧
    A.natDegree = m ∧ B.natDegree = m ∧
    C.natDegree = m ∧ D.natDegree = m

/-- Claim 38343: the zero-sum, zero-product discriminant branch recovers the
unordered factor pair on the exact characteristic-zero polynomial carrier. -/
def zeroSumZeroProductRecoversPair_claim38343 : Prop :=
  ∀ {K : Type*} [Field K] [CharZero K]
    (m : ℕ) (A B C D : Polynomial K),
    commonTwoFactorHypotheses m A B C D →
    twoFactorDerivativeEquality A B C D →
    A + B - C - D = 0 → A * B - C * D = 0 →
    unorderedFactorPair A B C D

/-- Claim 38344: the nonzero-product zero-sum branch has only the inherited
single-factor derivative ambiguity. -/
def zeroSumNonzeroProductInheritedAmbiguity_claim38344 : Prop :=
  ∀ {K : Type*} [Field K] [CharZero K]
    (m : ℕ) (A B C D : Polynomial K),
    commonTwoFactorHypotheses m A B C D →
    twoFactorDerivativeEquality A B C D →
    A + B - C - D = 0 → A * B - C * D ≠ 0 →
      (Polynomial.natDegree ((C - D) - (A - B)) = 0 ∧
        Polynomial.natDegree ((C - D) + (A - B)) = 0) ∧
      Polynomial.derivative A = Polynomial.derivative B ∧
      Polynomial.derivative C = Polynomial.derivative D ∧
      A + B = C + D

/-- Claim 38345: a nonzero constant sum difference forces the upper-half
collar in the two-factor discriminant identity. -/
def nonzeroSumUpperHalfCollar_claim38345 : Prop :=
  ∀ {K : Type*} [Field K] [CharZero K]
    (m : ℕ) (A B C D : Polynomial K),
    commonTwoFactorHypotheses m A B C D →
    twoFactorDerivativeEquality A B C D →
    A + B - C - D ≠ 0 →
    ∃ c₀ k₀ : K,
      c₀ ≠ 0 ∧
      A + B - C - D = Polynomial.C c₀ ∧
      A * B - C * D = Polynomial.C k₀ ∧
      Polynomial.natDegree (A + B) = m ∧
      Polynomial.natDegree
        (-2 * (A + B - C - D) * (A + B) +
          (A + B - C - D) ^ 2 + 4 * (A * B - C * D)) = m ∧
      Polynomial.natDegree ((C - D) - (A - B)) +
          Polynomial.natDegree ((C - D) + (A - B)) = m ∧
      max (Polynomial.natDegree (A - B)) (Polynomial.natDegree (C - D)) ≥
        (m + 1) / 2

/-- Claim 38346: the exact two-factor product-derivative setting has the
unordered-pair / inherited-single-factor / upper-half-degree trichotomy. -/
def mainTwoFactorTrichotomy_claim38346 : Prop :=
  ∀ {K : Type*} [Field K] [CharZero K]
    (m : ℕ) (A B C D : Polynomial K),
    commonTwoFactorHypotheses m A B C D →
    twoFactorDerivativeEquality A B C D →
      unorderedFactorPair A B C D ∨
      (Polynomial.derivative A = Polynomial.derivative B ∧
        Polynomial.derivative C = Polynomial.derivative D) ∨
      max (Polynomial.natDegree (A - B)) (Polynomial.natDegree (C - D)) ≥
        (m + 1) / 2

end

end MathlibPlus.Open.ResearchFormalization.R1373
