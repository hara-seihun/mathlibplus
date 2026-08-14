import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

noncomputable section

/-- The `n`th consecutive derivative of a real polynomial. -/
def consecutiveDerivative (n : ℕ) (f : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.derivative^[n]) f

/-- The signed centered consecutive-derivative determinant of rank `m`. -/
def karlinDet (m : ℕ) (f : Polynomial ℝ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m =>
      Polynomial.eval x (consecutiveDerivative (i.val + j.val) f))

/-- A positive-leading real polynomial all of whose complex zeros are nonpositive reals. -/
def positiveLeadingNonpositiveRealZeros (f : Polynomial ℝ) : Prop :=
  0 < f.leadingCoeff ∧
    ∀ z : ℂ,
      Polynomial.eval z (f.map Complex.ofRealHom) = 0 →
        ∃ r : ℝ, z = Complex.ofReal r ∧ r ≤ 0

/-- A negative rank witness at a nonnegative center. -/
def hasKarlinFailure (f : Polynomial ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ x : ℝ, 0 ≤ x ∧ karlinDet m f x < 0

/-- All signed consecutive-derivative determinants are nonnegative up to a degree. -/
def allRankNonnegativeThrough (d : ℕ) : Prop :=
  ∀ f : Polynomial ℝ,
    f.natDegree ≤ d →
      positiveLeadingNonpositiveRealZeros f →
        ∀ m : ℕ, 0 < m → ∀ x : ℝ, 0 ≤ x → 0 ≤ karlinDet m f x

/-- The boundary polynomial from the degree-seven rank-six counterexample. -/
def boundaryPolynomial : Polynomial ℝ :=
  Polynomial.X ^ 4 * (Polynomial.X + 1) ^ 3

/-- The value of `q` used for the simple-root counterexample. -/
def simpleRootQ : ℝ := (10 : ℝ) ^ 7

/-- The positive reciprocal roots used in the simple-root counterexample. -/
def simpleRootReciprocals : List ℝ :=
  [
    (53 * simpleRootQ - 3) / simpleRootQ,
    (53 * simpleRootQ - 1) / simpleRootQ,
    (53 * simpleRootQ + 1) / simpleRootQ,
    (53 * simpleRootQ + 3) / simpleRootQ,
    (simpleRootQ - 2) / simpleRootQ,
    1,
    (simpleRootQ + 2) / simpleRootQ
  ]

/-- The degree-seven product polynomial whose root magnitudes are the reciprocals displayed above. -/
def simpleRootPolynomial : Polynomial ℝ :=
  (simpleRootReciprocals.map
    (fun r : ℝ => Polynomial.C 1 + Polynomial.C r * Polynomial.X)).prod

/-- Every zero of a polynomial is simple and strictly negative. -/
def simpleStrictlyNegativeRoots (f : Polynomial ℝ) : Prop :=
  ∀ z : ℂ,
    Polynomial.eval z (f.map Complex.ofRealHom) = 0 →
      ∃ r : ℝ,
        z = Complex.ofReal r ∧ r < 0 ∧
          Polynomial.eval z ((f.map Complex.ofRealHom).derivative) ≠ 0

/--
Six is the sharp all-rank degree threshold for signed centered
consecutive-derivative determinants.
-/
def sharpAllRankDegreeThreshold : Prop :=
  allRankNonnegativeThrough 6 ∧
    (¬ ∃ f : Polynomial ℝ,
        f.natDegree < 7 ∧
          positiveLeadingNonpositiveRealZeros f ∧ hasKarlinFailure f) ∧
    boundaryPolynomial.natDegree = 7 ∧
      positiveLeadingNonpositiveRealZeros boundaryPolynomial ∧
      hasKarlinFailure boundaryPolynomial ∧
      karlinDet 6 boundaryPolynomial 0 = -(1246946918400 : ℝ) ∧
      (simpleRootReciprocals.Pairwise (· ≠ ·)) ∧
      (∀ r ∈ simpleRootReciprocals, 0 < r) ∧
      simpleRootPolynomial.natDegree = 7 ∧
      positiveLeadingNonpositiveRealZeros simpleRootPolynomial ∧
      simpleStrictlyNegativeRoots simpleRootPolynomial ∧
      karlinDet 6 simpleRootPolynomial 0 < 0

end

end MathlibPlus.Open.Analysis
