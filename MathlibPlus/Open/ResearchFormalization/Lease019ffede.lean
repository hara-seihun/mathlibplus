import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Lease019ffede

/-- The polynomial cross-ratio equation used by the three split claims. -/
def crossRatioEquation {A : Type*} [CommRing A] [Algebra ℚ A]
    (a b c d : Polynomial A) (lambda : ℚ) : Prop :=
  (a - d) * (b - c) =
    Polynomial.C (algebraMap ℚ A lambda) * ((a - c) * (b - d))

/-- The first coefficient index at which four coefficient streams are not constant. -/
def firstFourSplit {A : Type*} [Semiring A]
    (a b c d : Polynomial A) (h : ℕ) : Prop :=
  (∀ i < h,
      a.coeff i = b.coeff i ∧
      b.coeff i = c.coeff i ∧
      c.coeff i = d.coeff i) ∧
    ¬(a.coeff h = b.coeff h ∧
      b.coeff h = c.coeff h ∧
      c.coeff h = d.coeff h)

/-- The first coefficient index at which three coefficient streams are not constant. -/
def firstTripleSplit {A : Type*} [Semiring A]
    (a b c : Polynomial A) (k : ℕ) : Prop :=
  (∀ i < k, a.coeff i = b.coeff i ∧ b.coeff i = c.coeff i) ∧
    ¬(a.coeff k = b.coeff k ∧ b.coeff k = c.coeff k)

/-- Divisibility of all six pairwise differences by the first split monomial. -/
def allPairwiseDifferencesDivisible {A : Type*} [CommRing A]
    (a b c d : Polynomial A) (h : ℕ) : Prop :=
  Polynomial.X ^ h ∣ a - b ∧
  Polynomial.X ^ h ∣ a - c ∧
  Polynomial.X ^ h ∣ a - d ∧
  Polynomial.X ^ h ∣ b - c ∧
  Polynomial.X ^ h ∣ b - d ∧
  Polynomial.X ^ h ∣ c - d

/-- The coefficient equation obtained after the first-split reduction. -/
def coefficientCrossRatioEquation {A : Type*} [CommRing A] [Algebra ℚ A]
    (a b c d : Polynomial A) (h : ℕ) (lambda : ℚ) : Prop :=
  (a.coeff h - d.coeff h) * (b.coeff h - c.coeff h) =
    algebraMap ℚ A lambda *
      ((a.coeff h - c.coeff h) * (b.coeff h - d.coeff h))

/-- Pairwise distinctness of four coefficient values at one index. -/
def pairwiseDistinctFourCoefficients {A : Type*} [Semiring A]
    (a b c d : Polynomial A) (h : ℕ) : Prop :=
  a.coeff h ≠ b.coeff h ∧
  a.coeff h ≠ c.coeff h ∧
  a.coeff h ≠ d.coeff h ∧
  b.coeff h ≠ c.coeff h ∧
  b.coeff h ≠ d.coeff h ∧
  c.coeff h ≠ d.coeff h

/-- Claim 25211: the first nonconstant coefficient preserves the cross-ratio equation. -/
def claim25211 : Prop :=
  ∀ {A : Type*} [CommRing A] [IsDomain A] [Algebra ℚ A]
    (a b c d : Polynomial A) (lambda : ℚ) (h : ℕ),
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    lambda ≠ (0 : ℚ) ∧ lambda ≠ (1 : ℚ) ∧
    crossRatioEquation a b c d lambda ∧
    firstFourSplit a b c d h →
      allPairwiseDifferencesDivisible a b c d h ∧
      coefficientCrossRatioEquation a b c d h lambda

/-- Claim 25213: pairwise-distinct first-split coefficients obey the same cross ratio. -/
def claim25213 : Prop :=
  ∀ {A : Type*} [CommRing A] [IsDomain A] [Algebra ℚ A]
    (a b c d : Polynomial A) (lambda : ℚ) (h : ℕ),
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    lambda ≠ (0 : ℚ) ∧ lambda ≠ (1 : ℚ) ∧
    crossRatioEquation a b c d lambda ∧
    firstFourSplit a b c d h ∧
    pairwiseDistinctFourCoefficients a b c d h →
      coefficientCrossRatioEquation a b c d h lambda

/-- Claim 25215: a 3+1 first split descends to the stated affine relation. -/
def claim25215 : Prop :=
  ∀ {A : Type*} [CommRing A] [IsDomain A] [Algebra ℚ A]
    (a b c d : Polynomial A) (mu : ℚ) (h k : ℕ) (u v : A),
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    mu ≠ (0 : ℚ) ∧ mu ≠ (1 : ℚ) ∧
    h < k ∧
    crossRatioEquation a b c d mu ∧
    firstFourSplit a b c d h ∧
    a.coeff h = u ∧ b.coeff h = u ∧ c.coeff h = u ∧
    d.coeff h = v ∧ u ≠ v ∧
    firstTripleSplit a b c k →
      (u - v) * (b.coeff k - c.coeff k) =
          algebraMap ℚ A mu * (u - v) * (a.coeff k - c.coeff k) ∧
        b.coeff k - c.coeff k =
          algebraMap ℚ A mu * (a.coeff k - c.coeff k)

end MathlibPlus.Open.ResearchFormalization.Lease019ffede
