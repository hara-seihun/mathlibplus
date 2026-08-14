import Mathlib

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators ENNReal MeasureTheory Topology

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- The term `aₙ n⁻ˢ` of an ordinary complex Dirichlet series. -/
def dirichletTerm (a : ℕ+ → ℂ) (n : ℕ+) (s : ℂ) : ℂ :=
  a n * Complex.exp (-s * (Real.log (n.1 : ℝ) : ℂ))

/-- Positive-axis asymptotics for an absolutely convergent ordinary Dirichlet series. -/
def positiveAxisDirichletAsymptotics (a : ℕ+ → ℂ) (F : ℂ → ℂ) : Prop :=
  (∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Summable (fun n : ℕ+ => ‖dirichletTerm a n s‖) ∧
          F s = ∑' n : ℕ+, dirichletTerm a n s) →
    (Asymptotics.IsBigO atTop
        (fun σ : ℝ => F (σ : ℂ) - a 1)
        (fun σ : ℝ => Real.rpow 2 (-σ))) ∨
      ∃ n₀ : ℕ+,
        (2 : ℕ) ≤ n₀.1 ∧ a 1 = 0 ∧ a n₀ ≠ 0 ∧
          (∀ n : ℕ+, n.1 < n₀.1 → a n = 0) ∧
          Tendsto
            (fun σ : ℝ =>
              F (σ : ℂ) /
                (a n₀ * Complex.exp (-(σ : ℂ) * (Real.log (n₀.1 : ℝ) : ℂ))))
            atTop (𝓝 1)

/-- The complex point associated with the logarithm of a natural number. -/
def primeLogPoint (p : ℕ) : ℂ := (Real.log (p : ℝ) : ℂ)

/-- The usual prime-counting function, extended to real arguments. -/
def primeCountingAt (x : ℝ) : ℕ :=
  (Finset.filter (fun p : ℕ => Nat.Prime p ∧ (p : ℝ) ≤ x)
      (Finset.range (Nat.floor x + 1))).card

/-- The distinct prime logarithms lying in the disk of radius `R`. -/
def primeLogPointsInDisk (R : ℝ) : Finset ℂ := by
  classical
  exact Finset.image primeLogPoint
    (Finset.filter (fun p : ℕ => Nat.Prime p ∧ ‖primeLogPoint p‖ ≤ R)
      (Finset.range (Nat.floor (Real.exp R) + 1)))

/-- Exponential density and eventual power domination of prime logarithms. -/
def exponentialDensityOfPrimeLogarithms : Prop :=
  (∀ R : ℝ, ∀ p : ℕ, Nat.Prime p → (p : ℝ) ≤ Real.exp R →
      ‖primeLogPoint p‖ ≤ R) ∧
    (∀ R : ℝ, 0 ≤ R →
      (primeLogPointsInDisk R).card = primeCountingAt (Real.exp R)) ∧
    Asymptotics.IsEquivalent atTop
      (fun R : ℝ => (primeCountingAt (Real.exp R) : ℝ))
      (fun R : ℝ => Real.exp R / R) ∧
    (∀ d : ℕ, ∀ᶠ R : ℝ in atTop,
      R ^ d < (primeCountingAt (Real.exp R) : ℝ))

/-- A zero set has finite exponent of convergence when one positive exponent gives a
summable reciprocal-power series over its nonzero points. -/
def HasFiniteExponentOfConvergence (s : Set ℂ) : Prop :=
  ∃ q : ℝ, 0 < q ∧
    Summable
      (fun z : {z : ℂ // z ∈ s ∧ z ≠ 0} =>
        Real.rpow ‖(z : ℂ)‖ (-q))

/-- A zero set has infinite exponent of convergence when no positive exponent does so. -/
def HasInfiniteExponentOfConvergence (s : Set ℂ) : Prop :=
  ∀ q : ℝ, 0 < q →
    ¬ Summable
      (fun z : {z : ℂ // z ∈ s ∧ z ≠ 0} =>
        Real.rpow ‖(z : ℂ)‖ (-q))

def primeLogarithmSet : Set ℂ :=
  Set.range (fun p : {p : ℕ // Nat.Prime p} => primeLogPoint p.1)

/-- The explicit finite-order condition used for entire functions in this statement. -/
def EntireFiniteOrder (M : ℂ → ℂ) : Prop :=
  Differentiable ℂ M ∧
    ∃ ρ C R : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ R ∧
      ∀ z : ℂ, R ≤ ‖z‖ →
        ‖M z‖ ≤ Real.exp (C * Real.rpow ‖z‖ ρ)

/-- Prime logarithms as a uniqueness set for finite-order entire functions, together with
both exponent-of-convergence formulations in the claim. -/
def primeLogarithmFiniteOrderUniqueness : Prop :=
  HasInfiniteExponentOfConvergence primeLogarithmSet ∧
    (∀ M : ℂ → ℂ, EntireFiniteOrder M →
      (∀ p : ℕ, Nat.Prime p → M (primeLogPoint p) = 0) →
        ∀ z : ℂ, M z = 0) ∧
    (∀ M : ℂ → ℂ, EntireFiniteOrder M → (∃ z : ℂ, M z ≠ 0) →
      HasFiniteExponentOfConvergence {z : ℂ | M z = 0})

/-- The Laplace transform of a real signed measure carried by `[0,∞)`. -/
noncomputable def oneSidedLaplaceTransform
    (μ : SignedMeasure (Set.Ici (0 : ℝ))) (z : ℂ) : ℂ :=
  ∫ᵛ α, Complex.exp (-((α : ℝ) : ℂ) * z) ∂<•μ

def FiniteOneSidedSignedMeasure
    (μ : SignedMeasure (Set.Ici (0 : ℝ))) : Prop :=
  μ.totalVariation Set.univ ≠ ∞

/-- Finite one-sided signed measures have bounded holomorphic Laplace transforms. -/
def oneSidedSignedMeasureLaplaceBoundedHolomorphic : Prop :=
  ∀ μ : SignedMeasure (Set.Ici (0 : ℝ)),
    FiniteOneSidedSignedMeasure μ →
      DifferentiableOn ℂ (oneSidedLaplaceTransform μ) {z : ℂ | 0 < z.re} ∧
        ∀ z : ℂ, 0 < z.re →
          ‖oneSidedLaplaceTransform μ z‖ ≤
            μ.totalVariation.real Set.univ

/-- Uniqueness of the one-sided Laplace transform for finite real signed measures. -/
def oneSidedSignedMeasureLaplaceUniqueness : Prop :=
  ∀ μ : SignedMeasure (Set.Ici (0 : ℝ)),
    FiniteOneSidedSignedMeasure μ →
      ((∀ z : ℂ, 0 < z.re → oneSidedLaplaceTransform μ z = 0) → μ = 0) ∧
      (∀ a b : ℝ, 0 < a → a < b →
        (∀ x : ℝ, x ∈ Set.Icc a b →
          oneSidedLaplaceTransform μ (x : ℂ) = 0) → μ = 0)

/-- The integer adjacency matrix of a simple graph. -/
def graphAdjacencyMatrix {n : ℕ} (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℤ := by
  classical
  exact fun i j => if G.Adj i j then 1 else 0

/-- The multivariate matrix `t I - A_G - diag(x)`, with `none` naming `t`. -/
def graphPolynomialMatrix {n : ℕ} (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Option (Fin n)) ℤ) := by
  classical
  exact fun i j =>
    (if i = j then MvPolynomial.X none else 0) -
      MvPolynomial.C (graphAdjacencyMatrix G i j) -
      (if i = j then MvPolynomial.X (some i) else 0)

def graphPolynomial {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (Option (Fin n)) ℤ :=
  Matrix.det (graphPolynomialMatrix G)

/-- The induced `t I - A_G[U]` determinant, still viewed in the `t`-variable of the
multivariate coefficient ring. -/
def inducedGraphPolynomial {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) : MvPolynomial (Option (Fin n)) ℤ := by
  classical
  exact Matrix.det (fun i j : U =>
    (if i = j then MvPolynomial.X none else 0) -
      MvPolynomial.C (if G.Adj (i : Fin n) (j : Fin n) then 1 else 0))

def graphVariableMonomial {n : ℕ} (U : Finset (Fin n)) :
    Option (Fin n) →₀ ℕ := by
  classical
  exact (Finset.univ \ U).sum (fun i => Finsupp.single (some i) 1)

def graphCoefficientMonomial {n : ℕ} (U : Finset (Fin n)) (k : ℕ) :
    Option (Fin n) →₀ ℕ :=
  Finsupp.single none k + graphVariableMonomial U

def inducedGraphCoefficient {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) (k : ℕ) : ℤ :=
  MvPolynomial.coeff (Finsupp.single none k) (inducedGraphPolynomial G U)

def graphCoefficient {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) (k : ℕ) : ℤ :=
  MvPolynomial.coeff (graphCoefficientMonomial U k) (graphPolynomial G)

def graphExpansionRhs {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (Option (Fin n)) ℤ := by
  classical
  exact (Finset.univ : Finset (Finset (Fin n))).sum (fun U =>
    (-1 : MvPolynomial (Option (Fin n)) ℤ) ^ (n - U.card) *
      MvPolynomial.monomial (graphVariableMonomial U) 1 *
        inducedGraphPolynomial G U)

/-- Exact determinant expansion, coefficient extraction, and the pair edge certificate. -/
def graphDeterminantExpansionAndPairCertificate : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    graphPolynomial G = graphExpansionRhs G ∧
      (∀ U : Finset (Fin n), ∀ k : ℕ,
        graphCoefficient G U k =
          ((-1 : ℤ) ^ (n - U.card)) * inducedGraphCoefficient G U k) ∧
      (∀ i j : Fin n, i ≠ j →
        graphAdjacencyMatrix G i j =
          ((-1 : ℤ) ^ (n - 1)) * graphCoefficient G {i, j} 0)

def relabelGraph {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.comap σ G

def graphPolynomialOrbit {n : ℕ} (G : SimpleGraph (Fin n)) :
    Set (MvPolynomial (Option (Fin n)) ℤ) :=
  {Q | ∃ σ : Equiv.Perm (Fin n), Q = graphPolynomial (relabelGraph G σ)}

def GraphsIsomorphic {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    ∀ i j : Fin n, G.Adj i j ↔ H.Adj (σ i) (σ j)

/-- The simultaneous relabelling orbit of the multivariate polynomial has singleton fibres. -/
def multivariateGraphMapSingletonFibres : Prop :=
  (∀ n : ℕ, ∀ G H : SimpleGraph (Fin n),
    graphPolynomialOrbit G = graphPolynomialOrbit H ↔ GraphsIsomorphic G H) ∧
  (∀ n : ℕ, ∀ G H : SimpleGraph (Fin n),
    graphPolynomialOrbit G = graphPolynomialOrbit H → GraphsIsomorphic G H)

/-- Total nonnegativity and strict total nonnegativity over the real nonnegative cone. -/
def IsTotallyNonnegative {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, ∀ r : Fin k → Fin m, ∀ c : Fin k → Fin n,
    StrictMono r → StrictMono c →
      0 ≤ Matrix.det (A.submatrix r c)

def IsStrictlyTotallyNonnegative {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, ∀ r : Fin k → Fin m, ∀ c : Fin k → Fin n,
    StrictMono r → StrictMono c →
      0 < Matrix.det (A.submatrix r c)

def transitionT0 : Matrix (Fin 1) (Fin 2) ℝ := by
  classical
  exact fun _ j => if j = 0 then 1 else 10

def transitionT1 : Matrix (Fin 2) (Fin 3) ℝ := by
  classical
  exact fun i j =>
    if i = 0 then (if j = 0 then 1 else if j = 1 then 2 else 3)
    else (if j = 0 then 1 else if j = 1 then 3 else 5)

def stackedTransitionRows : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact fun i j =>
    if i = 0 then (if j = 0 then 1 else 0)
    else if i = 1 then (if j = 0 then 1 else if j = 1 then 10 else 0)
    else (if j = 0 then 11 else if j = 1 then 32 else 53)

def relevantStackRows : Fin 2 → Fin 3 := by
  classical
  exact fun r => if r = 0 then 1 else 2

def relevantStackColumns : Fin 2 → Fin 3 := by
  classical
  exact fun c => if c = 0 then 0 else 1

/-- The displayed strictly-TN transition counterexample and its negative minor. -/
def strictlyTNTransitionsCanProduceNonTNStack : Prop :=
  IsStrictlyTotallyNonnegative transitionT0 ∧
    IsStrictlyTotallyNonnegative transitionT1 ∧
    Matrix.det (stackedTransitionRows.submatrix relevantStackRows relevantStackColumns) = -78 ∧
    ¬ IsTotallyNonnegative stackedTransitionRows

end MathlibPlus.Open.ResearchFormalization.Batch
