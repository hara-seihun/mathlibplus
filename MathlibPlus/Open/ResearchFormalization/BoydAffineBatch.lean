import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators
noncomputable section

/-- Evaluation of a real polynomial at a complex point. -/
def evalRealComplex (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℝ ℂ) z p

/-- Evaluation of an integral polynomial at a complex point. -/
def evalIntComplex (p : Polynomial ℤ) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℤ ℂ) z p

/-- The real polynomial obtained from an integral trace polynomial. -/
def traceToReal (ell : Polynomial ℤ) : Polynomial ℝ :=
  ell.map (algebraMap ℤ ℝ)

/-- Degree at most `n - 1`, with the zero polynomial treated in the usual way. -/
def degreeAtMost (p : Polynomial ℝ) (n : ℕ) : Prop :=
  p = 0 ∨ p.natDegree < n

/-- The Salem root geometry used here is stated explicitly rather than hidden in a
named predicate. -/
def isSalemPolynomial (R : Polynomial ℤ) (n : ℕ) : Prop :=
  R.Monic ∧
    R.natDegree = 2 * n ∧
    Irreducible R ∧
    ∃ θ : ℝ,
      1 < θ ∧
        evalIntComplex R (θ : ℂ) = 0 ∧
          evalIntComplex R ((θ : ℂ)⁻¹) = 0 ∧
            ∀ z : ℂ,
              evalIntComplex R z = 0 →
                z = (θ : ℂ) ∨ z = ((θ : ℂ)⁻¹) ∨ ‖z‖ = 1

/-- The reciprocal trace-lift relation in the Laurent domain, expressed by its
values at every nonzero complex point. -/
def traceLift (R ell : Polynomial ℤ) (n : ℕ) : Prop :=
  ell.Monic ∧
    ell.natDegree = n ∧
      ∀ z : ℂ,
        z ≠ 0 →
          evalIntComplex R z =
            z ^ n * evalIntComplex ell (z + z⁻¹)

/-- The two equivalent pointwise definitions of an affine Boyd member. -/
def affineBoydFormula
    (n : ℕ) (ell c q A : Polynomial ℝ) : Prop :=
  degreeAtMost c n ∧
    q = ell - (2 : Polynomial ℝ) * c ∧
      ∀ z : ℂ,
        z ≠ 0 →
          (evalRealComplex A z =
              z ^ n *
                (z * evalRealComplex q (z + z⁻¹) +
                  (z + z⁻¹) * evalRealComplex c (z + z⁻¹))) ∧
            (evalRealComplex A z =
              z ^ n *
                (z * evalRealComplex ell (z + z⁻¹) +
                  (z⁻¹ - z) * evalRealComplex c (z + z⁻¹)))

/-- Claim 25787: the affine Boyd construction, including the Salem trace lift,
its correction polynomial, and both displayed formulas for the member. -/
def claim25787 : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ),
    (isSalemPolynomial R n ∧ traceLift R ell n) →
      ∀ c : Polynomial ℝ,
        degreeAtMost c n →
          ∃ q A : Polynomial ℝ,
            affineBoydFormula n (traceToReal ell) c q A

/-- The phase-normalized value of a Boyd member. -/
def phaseNormalized
    (n : ℕ) (φ : ℝ) (A : Polynomial ℝ) : ℂ :=
  Complex.exp (-((n : ℂ) * Complex.I * (φ : ℂ))) *
    evalRealComplex A (Complex.exp (Complex.I * (φ : ℂ)))

/-- Claim 25788: the real and imaginary phase identities. -/
def claim25788 : Prop :=
  ∀ (n : ℕ) (ell c q A : Polynomial ℝ),
    affineBoydFormula n ell c q A →
      ∀ φ : ℝ,
        let t : ℝ := 2 * Real.cos φ
        Complex.re (phaseNormalized n φ A) =
              t * Polynomial.eval t ell / 2 ∧
          Complex.im (phaseNormalized n φ A) =
              Real.sin φ * Polynomial.eval t q

/-- A unit-circle zero of a real polynomial. -/
def hasUnitCircleRoot (A : Polynomial ℝ) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ evalRealComplex A z = 0

/-- The interior affine walls in the trace coordinate. -/
def interiorTraceWall
    (ell c : Polynomial ℝ) : Prop :=
  ∃ u : ℝ,
    -2 < u ∧ u < 2 ∧ u ≠ 0 ∧
      Polynomial.eval u ell = 0 ∧ Polynomial.eval u c = 0

/-- Claim 25789: under the two endpoint exclusions, the displayed walls are
exactly the unit-circle-root locus. -/
def claim25789 : Prop :=
  ∀ (n : ℕ) (ell c q A : Polynomial ℝ),
    affineBoydFormula n ell c q A →
      (Polynomial.eval 2 ell ≠ 0 ∧
          Polynomial.eval (-2) ell ≠ 0) →
        (hasUnitCircleRoot A ↔
          interiorTraceWall ell c ∨ Polynomial.eval 0 q = 0)

end
end MathlibPlus.Open.ResearchFormalization
