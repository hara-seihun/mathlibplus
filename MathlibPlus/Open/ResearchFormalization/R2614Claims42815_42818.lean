import Mathlib
import Mathlib.Algebra.Polynomial.Laurent

namespace MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

noncomputable section

open scoped BigOperators
open LaurentPolynomial

abbrev Part (m : ℕ) := Fin m → ℕ
abbrev IntFunction (m : ℕ) := (Fin m → ℤ) → ℚ
abbrev IntPolyFunction (m : ℕ) := (Fin m → ℤ) → Polynomial ℚ
abbrev RatFunction (m : ℕ) := Part m → ℚ
abbrev RatPolyFunction (m : ℕ) := Part m → Polynomial ℚ

/-- Coefficientwise nonnegativity in the half-shift variable. -/
def coefficientwiseNonnegative (P : Polynomial ℚ) : Prop :=
  ∀ n : ℕ, 0 ≤ P.coeff n

/-- Positive-row partitions are written top-to-bottom, with the dimension
bound attached to the corresponding row index. -/
def admissiblePartition (d m : ℕ) (p : Part m) : Prop :=
  m ≤ d ∧
    (∀ i : Fin m, 1 ≤ p i ∧ p i + i.1 ≤ d) ∧
      ∀ ⦃i j : Fin m⦄, i.1 < j.1 → p j ≤ p i

/-- Lower a selected collection of partition coordinates once. -/
def lowerPart {m : ℕ} (p : Part m) (J : Finset (Fin m)) : Part m :=
  fun k => p k - if k ∈ J then 1 else 0

def lowerPartOne {m : ℕ} (p : Part m) (i : Fin m) : Part m :=
  lowerPart p ({i} : Finset (Fin m))

/-- Every vertex of the indicated Boolean cube is an admissible partition. -/
def admissibleCube {m : ℕ} (d : ℕ) (p : Part m) (I : Finset (Fin m)) : Prop :=
  ∀ J : Finset (Fin m), J ⊆ I → admissiblePartition d m (lowerPart p J)

/-- The row coordinate is the bottom-to-top partition coordinate from the
admitted maximal-Riordan-minor description. -/
def rowCoordinate {m : ℕ} (p : Part m) (i : Fin m) : ℤ :=
  (p (Fin.rev i) : ℤ) + (i.1 : ℤ)

/-- Laurent coefficients are used so that the skipped offset -1 is a genuine
column offset rather than an unmentioned natural-number restriction. -/
def rowUniformLaurentKernel (R : ℕ) (q s : ℤ) : ℚ :=
  ((LaurentPolynomial.C (1 : ℚ) + LaurentPolynomial.C 2 * LaurentPolynomial.T 1) *
      LaurentPolynomial.T s * Polynomial.toLaurent
        ((1 + Polynomial.X : Polynomial ℚ) ^
          Int.toNat ((R : ℤ) + s - 1))).coeff q

def consecutiveOffsets (m : ℕ) : Fin m → ℤ :=
  fun j => (j.1 : ℤ)

def skippedFourOffsets : Fin 4 → ℤ :=
  fun j => if j.1 = 0 then (-1 : ℤ) else (j.1 : ℤ)

/-- The determinant of the kernel matrix with a fixed offset list. -/
def kernelMinor {m : ℕ} (R : ℕ) (offsets : Fin m → ℤ) (p : Part m) : ℚ :=
  Matrix.det (fun i j =>
    rowUniformLaurentKernel R (rowCoordinate p i) (offsets j))

def nativeFiveMinor (d : ℕ) (p : Part 5) : ℚ :=
  kernelMinor (d - 4) (consecutiveOffsets 5) p

def nativeFourMinor (d : ℕ) (p : Part 4) : ℚ :=
  kernelMinor (d - 3) (consecutiveOffsets 4) p

def skippedFourMinor (R : ℕ) (p : Part 4) : ℚ :=
  kernelMinor R skippedFourOffsets p

/-- The same determinant when its bottom-to-top row coordinates are
supplied directly. -/
def kernelMinorRows {m : ℕ} (R : ℕ) (offsets : Fin m → ℤ)
    (q : Fin m → ℤ) : ℚ :=
  Matrix.det (fun i j => rowUniformLaurentKernel R (q i) (offsets j))

/-- Integer-indexed lowering for the operator identity in Claim 42816. -/
def lowerInt {m : ℕ} (q : Fin m → ℤ) (i : Fin m) : Fin m → ℤ :=
  fun k => if k = i then q k - 1 else q k

def lowerIntSet {m : ℕ} (q : Fin m → ℤ) (J : Finset (Fin m)) : Fin m → ℤ :=
  fun k => q k - if k ∈ J then 1 else 0

def applyIntRatOperators {m : ℕ}
    (ops : List (IntFunction m → IntFunction m))
    (F : IntFunction m) : IntFunction m :=
  ops.foldr (fun op G => op G) F

def intShiftOperator {m : ℕ} (i : Fin m) (F : IntFunction m) : IntFunction m :=
  fun q => F (lowerInt q i)

def intPartialOperator {m : ℕ} (R : ℕ) (i : Fin m)
    (F : IntFunction m) : IntFunction m :=
  fun q =>
    ((R : ℚ) + (q i : ℚ)) * F (lowerInt q i) - F q

def mixedIntPartial {m : ℕ} (R : ℕ) (I : Finset (Fin m))
    (F : IntFunction m) : IntFunction m :=
  applyIntRatOperators
    (I.toList.map (fun i => intPartialOperator R i)) F

/-- The strict, nonnegative row-domain convention used for the kernel
minor cubes.  A bottom row may be lowered only when it starts at least one
above zero. -/
def admissibleKernelCube {m : ℕ} (q : Fin m → ℤ)
    (I : Finset (Fin m)) : Prop :=
  (∀ i : Fin m, 0 ≤ q i) ∧
    StrictMono q ∧
      (∀ i : Fin m, i.1 = 0 → (i ∉ I ∨ 1 ≤ q i)) ∧
        ∀ J : Finset (Fin m), J ⊆ I →
          StrictMono (lowerIntSet q J) ∧
            ∀ i : Fin m, 0 ≤ lowerIntSet q J i

/-- A canonical increasing-order application of a family of commuting
coordinate operators. -/
def applyRatOperators {m : ℕ}
    (ops : List (RatFunction m → RatFunction m))
    (F : RatFunction m) : RatFunction m :=
  ops.foldr (fun op G => op G) F

def weightedDifference {m : ℕ} (d : ℕ) (i : Fin m)
    (F : RatFunction m) : RatFunction m :=
  fun p =>
    ((d : ℚ) + (p i : ℚ) - (i.1 : ℚ)) * F (lowerPartOne p i) - F p

def mixedWeightedDifference {m : ℕ} (d : ℕ) (I : Finset (Fin m))
    (F : RatFunction m) : RatFunction m :=
  applyRatOperators (I.toList.map (fun i => weightedDifference d i)) F

def applyPolyOperators {m : ℕ}
    (ops : List (RatPolyFunction m → RatPolyFunction m))
    (F : RatPolyFunction m) : RatPolyFunction m :=
  ops.foldr (fun op G => op G) F

def weightedPolynomialDifference {m : ℕ} (d : ℕ) (i : Fin m)
    (F : RatPolyFunction m) : RatPolyFunction m :=
  fun p =>
    (2 * Polynomial.X +
        Polynomial.C ((d : ℚ) + (p i : ℚ) - (i.1 : ℚ))) *
        F (lowerPartOne p i) - F p

def mixedPolynomialDifference {m : ℕ} (d : ℕ) (I : Finset (Fin m))
    (F : RatPolyFunction m) : RatPolyFunction m :=
  applyPolyOperators (I.toList.map (fun i => weightedPolynomialDifference d i)) F

/-- Claim 42815: all-rank complete monotonicity of the native five-row
minor and the skipped four-row minor. -/
def claim42815 : Prop :=
  (∀ R : ℕ, 1 ≤ R →
    ∀ q : Fin 5 → ℤ, StrictMono q →
      ∀ I : Finset (Fin 5), I.Nonempty →
        admissibleKernelCube q I →
          0 ≤ mixedIntPartial R I
            (fun rows => kernelMinorRows R (consecutiveOffsets 5) rows) q) ∧
  (∀ R : ℕ, 2 ≤ R →
    ∀ q : Fin 4 → ℤ, StrictMono q →
      ∀ I : Finset (Fin 4),
        admissibleKernelCube q I →
          0 ≤ mixedIntPartial R I
            (fun rows => kernelMinorRows R skippedFourOffsets rows) q)

def intShiftPartial {m : ℕ} (R : ℕ) (I J : Finset (Fin m))
    (F : IntFunction m) : IntFunction m :=
  applyIntRatOperators
    ((I \ J).toList.map (fun i => intShiftOperator i))
    (applyIntRatOperators
      (J.toList.map (fun i => intPartialOperator R i)) F)

def applyIntPolyOperators {m : ℕ}
    (ops : List (IntPolyFunction m → IntPolyFunction m))
    (F : IntPolyFunction m) : IntPolyFunction m :=
  ops.foldr (fun op G => op G) F

def intPolynomialDifferenceOperator {m : ℕ} (R : ℕ) (i : Fin m)
    (F : IntPolyFunction m) : IntPolyFunction m :=
  fun q =>
    (Polynomial.X + Polynomial.C ((R : ℚ) + (q i : ℚ))) *
        F (lowerInt q i) - F q

def intPolynomialDifferenceOperatorB {m : ℕ} (R : ℕ) (i : Fin m)
    (F : IntPolyFunction m) : IntPolyFunction m :=
  fun q =>
    (2 * Polynomial.X + Polynomial.C ((R : ℚ) + (q i : ℚ))) *
        F (lowerInt q i) - F q

def mixedIntPolynomialDifference {m : ℕ} (R : ℕ) (I : Finset (Fin m))
    (F : IntFunction m) : IntPolyFunction m :=
  applyIntPolyOperators
    (I.toList.map (fun i => intPolynomialDifferenceOperator R i))
    (fun q => Polynomial.C (F q))

def mixedIntPolynomialDifferenceB {m : ℕ} (R : ℕ) (I : Finset (Fin m))
    (F : IntFunction m) : IntPolyFunction m :=
  applyIntPolyOperators
    (I.toList.map (fun i => intPolynomialDifferenceOperatorB R i))
    (fun q => Polynomial.C (F q))

def intExpansion {m : ℕ} (R : ℕ) (I : Finset (Fin m))
    (F : IntFunction m) : IntPolyFunction m :=
  fun q =>
    Finset.sum I.powerset (fun J =>
      Polynomial.X ^ (I.card - J.card) *
        Polynomial.C (intShiftPartial R I J F q))

def intExpansionB {m : ℕ} (R : ℕ) (I : Finset (Fin m))
    (F : IntFunction m) : IntPolyFunction m :=
  fun q =>
    Finset.sum I.powerset (fun J =>
      (2 * Polynomial.X) ^ (I.card - J.card) *
        Polynomial.C (intShiftPartial R I J F q))

/-- Claim 42816: the commuting x-dependent operator expansion, together
with its coefficientwise consequence in x and after x=2b. -/
def claim42816 : Prop :=
  ∀ (m R : ℕ) (I : Finset (Fin m)) (F : IntFunction m),
    mixedIntPolynomialDifference R I F = intExpansion R I F ∧
      mixedIntPolynomialDifferenceB R I F = intExpansionB R I F ∧
        ((∀ J ∈ I.powerset, ∀ q : Fin m → ℤ,
            0 ≤ intShiftPartial R I J F q) →
          (∀ q : Fin m → ℤ,
            coefficientwiseNonnegative (intExpansion R I F q) ∧
              coefficientwiseNonnegative (intExpansionB R I F q)))

def nativeFivePolynomialFunction (d : ℕ) : RatPolyFunction 5 :=
  fun p => Polynomial.C (nativeFiveMinor d p)

def fourToFiveBoundary (d : ℕ) (p : Part 4) : Polynomial ℚ :=
  (2 * Polynomial.X + Polynomial.C (d - 3 : ℚ)) *
      Polynomial.C (nativeFourMinor d p) -
    Polynomial.C (nativeFiveMinor d (Fin.snoc p 1))

/-- Claim 42817: the native five-row amplitude has coefficientwise
nonnegative x=2b mixed weighted differences on every admissible cube. -/
def claim42817 : Prop :=
  ∀ d : ℕ, 5 ≤ d →
    ∀ p : Part 5, admissiblePartition d 5 p →
      ∀ I : Finset (Fin 5), I.Nonempty →
        admissibleCube d p I →
          coefficientwiseNonnegative
            (mixedPolynomialDifference d I
              (nativeFivePolynomialFunction d) p)

/-- Claim 42818: the four-to-five bottom-one boundary has the same
coefficientwise complete weighted monotonicity, including the empty cube. -/
def claim42818 : Prop :=
  ∀ d : ℕ, 5 ≤ d →
    ∀ p : Part 4, admissiblePartition d 4 p →
      ∀ I : Finset (Fin 4), admissibleCube d p I →
        coefficientwiseNonnegative
          (mixedPolynomialDifference d I
            (fun q => fourToFiveBoundary d q) p)

end

end MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818
