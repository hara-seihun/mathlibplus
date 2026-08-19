import MathlibPlus.Open.Algebra.PrimitiveSeedTowers50215

open scoped BigOperators

namespace MathlibPlus.Open.Algebra

noncomputable section

abbrev Claim50211Polynomial := Claim50215Polynomial

/-- Ordinary component count of a monomial exponent. -/
def claim50211OrdinaryDegree (e : ℕ+ →₀ ℕ) : ℕ :=
  e.sum (fun _ a => a)

/-- The ordinary-degree row of a component-size polynomial. -/
def claim50211DegreeRow (d : ℕ) (p : Claim50211Polynomial) : Claim50211Polynomial :=
  p.support.sum (fun e =>
    if claim50211OrdinaryDegree e = d then
      MvPolynomial.monomial e (MvPolynomial.coeff e p)
    else 0)

/-- A polynomial has no singleton variable in any supported monomial. -/
def claim50211X1Free (p : Claim50211Polynomial) : Prop :=
  ∀ e ∈ p.support, e (1 : ℕ+) = 0

/-- The degree-`d` row divisible by the singleton variable. -/
def claim50211X1DivisibleRow (d : ℕ) (p : Claim50211Polynomial) :
    Claim50211Polynomial :=
  (p.support.filter (fun e =>
    claim50211OrdinaryDegree e = d ∧ 0 < e (1 : ℕ+))).sum (fun e =>
      MvPolynomial.monomial e (MvPolynomial.coeff e p))

/-- Divide a polynomial row by one factor of the singleton variable. -/
def claim50211DivideX1 (p : Claim50211Polynomial) : Claim50211Polynomial :=
  (p.support.filter (fun e => 0 < e (1 : ℕ+))).sum (fun e =>
    MvPolynomial.monomial
      (e - Finsupp.single (1 : ℕ+) 1) (MvPolynomial.coeff e p))

/-- Claim 50211: the exact algebraic pendant operator is typed between the
weight sectors for all positive indices, with the tree-side range restricted
as stated and the algebraic unit normalization at index one. -/
def claim50211_pendantDefectOperator : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    ∀ p : Claim50211Polynomial,
      claim50215WeightN (n - 1) p →
        claim50215WeightN n (claim50215PendantOperator n p)) ∧
  (∀ n : ℕ, 2 ≤ n →
    ∀ p : Claim50211Polynomial,
      claim50215WeightN (n - 1) p →
        claim50215WeightN n (claim50215PendantOperator n p)) ∧
  claim50215PendantOperator 1 (1 : Claim50211Polynomial) =
    MvPolynomial.X 1

/-- The leading-row scalar in the ordinary-degree filtration. -/
def claim50213LeadingCoefficient (n k : ℕ) : ℚ :=
  (n : ℚ) * ((k : ℚ) - 1) + 2

/-- The degree-`k` row is the maximal nonzero row of a polynomial. -/
def claim50213MaximalRow (k : ℕ) (p : Claim50211Polynomial) : Prop :=
  claim50211DegreeRow k p ≠ 0 ∧
    ∀ d : ℕ, k < d → claim50211DegreeRow d p = 0

/-- Claim 50213: triangular leading rows, positivity, injectivity, zero
intersection with the no-singleton sector, and the exact image-plus-sector
split on the concrete weight-graded polynomial carrier. -/
def claim50213_pendantOperatorTriangularSplit : Prop :=
  (∀ (n k : ℕ) (f : Claim50211Polynomial),
    1 ≤ n →
    claim50215WeightN (n - 1) f →
    claim50213MaximalRow k f →
      claim50211DegreeRow (k + 1) (claim50215PendantOperator n f) =
          claim50213LeadingCoefficient n k •
            (MvPolynomial.X 1 * claim50211DegreeRow k f) ∧
        ∀ d : ℕ, k + 1 < d →
          claim50211DegreeRow d (claim50215PendantOperator n f) = 0) ∧
  (∀ (n k : ℕ), 1 ≤ k → 0 < claim50213LeadingCoefficient n k) ∧
  claim50213LeadingCoefficient 1 0 = 1 ∧
  (∀ n : ℕ, 1 ≤ n →
    ∀ p q : Claim50211Polynomial,
      claim50215WeightN (n - 1) p →
      claim50215WeightN (n - 1) q →
      claim50215PendantOperator n p = claim50215PendantOperator n q →
        p = q) ∧
  (∀ n : ℕ, 1 ≤ n →
    ∀ p q : Claim50211Polynomial,
      claim50215WeightN (n - 1) p →
      claim50215WeightN n q →
      claim50215PendantOperator n p = q →
      claim50211X1Free q →
        p = 0 ∧ q = 0) ∧
  (∀ n : ℕ, 1 ≤ n →
    ∀ h : Claim50211Polynomial,
      claim50215WeightN n h →
        ∃! q : Claim50211Polynomial,
          claim50215WeightN n q ∧
            claim50211X1Free q ∧
            ∃ f : Claim50211Polynomial,
              claim50215WeightN (n - 1) f ∧
                h = claim50215PendantOperator n f + q)

/-- The row selected by one step of the stated descending elimination. -/
def claim50214EliminationTerm
    (n d : ℕ) (r : ℕ → Claim50211Polynomial) : Claim50211Polynomial :=
  ((n : ℚ) * ((d - 2 : ℕ) : ℚ) + 2)⁻¹ •
    claim50211DivideX1 (claim50211X1DivisibleRow d (r d))

/-- The residual update after removing the selected leading row. -/
def claim50214ResidualStep
    (n d : ℕ) (r : ℕ → Claim50211Polynomial) : Claim50211Polynomial :=
  r d - claim50215PendantOperator n (claim50214EliminationTerm n d r)

/-- The sum of all source rows selected during the finite descent. -/
def claim50214AccumulatedSource
    (n : ℕ) (r : ℕ → Claim50211Polynomial) : Claim50211Polynomial :=
  Finset.sum ((Finset.range (n + 1)).filter (fun d => 2 ≤ d))
    (fun d => claim50214EliminationTerm n d r)

/-- A residual sequence is tied to its initial polynomial, every row update,
its typed source rows, the row-level action, and its final no-singleton
remainder. -/
def claim50214ResidualRun
    (n : ℕ) (h : Claim50211Polynomial) (r : ℕ → Claim50211Polynomial) : Prop :=
  r n = h ∧
  (∀ d : ℕ, 2 ≤ d → d ≤ n →
    r (d - 1) = claim50214ResidualStep n d r) ∧
  (∀ d : ℕ, d ≤ n → claim50215WeightN n (r d)) ∧
  (∀ d : ℕ, 2 ≤ d → d ≤ n →
    claim50215WeightN (n - 1) (claim50214EliminationTerm n d r)) ∧
  (∀ d : ℕ, 2 ≤ d → d ≤ n →
    claim50211DegreeRow d (r (d - 1)) =
      claim50211DegreeRow d (r d) -
        claim50211X1DivisibleRow d (r d)) ∧
  (∀ d e : ℕ, 2 ≤ d → d ≤ n → e ≠ d → e ≠ d - 1 →
    claim50211DegreeRow e (claim50215PendantOperator n
      (claim50214EliminationTerm n d r)) = 0) ∧
  claim50211X1Free (r 1) ∧
  h = claim50215PendantOperator n (claim50214AccumulatedSource n r) + r 1

/-- Linearity on the weight-`n` sector for the resulting projection. -/
def claim50214_pendantProjectionLinearity
    (n : ℕ) (π : Claim50211Polynomial → Claim50211Polynomial) : Prop :=
  (∀ h g : Claim50211Polynomial,
    claim50215WeightN n h → claim50215WeightN n g →
      π (h + g) = π h + π g) ∧
  (∀ (c : ℚ) (h : Claim50211Polynomial),
    claim50215WeightN n h → π (c • h) = c • π h)

/-- Claim 50214: the connected descending row elimination, its unique
no-singleton remainder, and the resulting typed linear projection and kernel. -/
def claim50214_x1FreeRowReduction : Prop :=
  (∀ (n : ℕ), 1 ≤ n →
    ∀ h : Claim50211Polynomial, claim50215WeightN n h →
      (n = 1 →
        ∃ f : Claim50211Polynomial,
          claim50215WeightN 0 f ∧ h = claim50215PendantOperator 1 f ∧
            ∃! q : Claim50211Polynomial,
              q = 0 ∧ claim50211X1Free q ∧ h =
                claim50215PendantOperator 1 f + q) ∧
      (2 ≤ n →
        ∃ r : ℕ → Claim50211Polynomial,
          claim50214ResidualRun n h r ∧
          ∃! q : Claim50211Polynomial,
            claim50215WeightN n q ∧ claim50211X1Free q ∧
              ∃ f : Claim50211Polynomial,
                claim50215WeightN (n - 1) f ∧
                  h = claim50215PendantOperator n f + q)) ∧
  (∀ (n : ℕ), 1 ≤ n →
    ∃ π : Claim50211Polynomial → Claim50211Polynomial,
      (∀ h : Claim50211Polynomial,
        claim50215WeightN n h →
          claim50215WeightN n (π h) ∧ claim50211X1Free (π h) ∧
            ∃ f : Claim50211Polynomial,
              claim50215WeightN (n - 1) f ∧
                h = claim50215PendantOperator n f + π h) ∧
      (∀ h : Claim50211Polynomial,
        claim50215WeightN n h →
          (π h = 0 ↔
            ∃ f : Claim50211Polynomial,
              claim50215WeightN (n - 1) f ∧
                h = claim50215PendantOperator n f)) ∧
      claim50214_pendantProjectionLinearity n π ∧
      (∀ h : Claim50211Polynomial,
        claim50215WeightN n h → π (π h) = π h) ∧
      (∀ h : Claim50211Polynomial,
        claim50215WeightN n h → claim50211X1Free h → π h = h) ∧
      (∀ h : Claim50211Polynomial,
        claim50215WeightN n h →
          (n = 1 → π h = 0) ∧
          (2 ≤ n →
            ∃ r : ℕ → Claim50211Polynomial,
              claim50214ResidualRun n h r ∧ π h = r 1)))

end

end MathlibPlus.Open.Algebra
