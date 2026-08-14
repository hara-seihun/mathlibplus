import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section
  open Classical

  /-- The zero-additive-constant representative of the GHS source potential. -/
  def ghsSourcePotential (σ u : ℝ) : ℝ :=
    u ^ 2 / (2 * σ ^ 2) - Real.log (2 + Real.cosh (u / σ ^ 2))

  /-- Exact third-derivative and convexity content of the GHS-strength claim. -/
  def ghsStrengthPotentialConvexity : Prop :=
    ∀ σ : ℝ, 0 < σ →
      (∀ u : ℝ,
        iteratedDeriv 3 (ghsSourcePotential σ) u =
          (2 * (Real.cosh (u / σ ^ 2) - 1) * Real.sinh (u / σ ^ 2)) /
            (σ ^ 6 * (2 + Real.cosh (u / σ ^ 2)) ^ 3)) ∧
      (∀ u : ℝ, 0 < u →
        0 < (2 * (Real.cosh (u / σ ^ 2) - 1) * Real.sinh (u / σ ^ 2)) /
          (σ ^ 6 * (2 + Real.cosh (u / σ ^ 2)) ^ 3)) ∧
      StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (deriv (ghsSourcePotential σ)) ∧
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (deriv (ghsSourcePotential σ)) ∧
      ContinuousOn (deriv (ghsSourcePotential σ)) (Set.Ici (0 : ℝ))

  /-- The three-atom even moment sequence. -/
  def threeAtomMoment (w x : Fin 3 → ℝ) (k : ℕ) : ℝ :=
    ∑ j : Fin 3, w j * (x j) ^ (2 * k)

  /-- The principal Hankel matrix of a sequence, with indices starting at zero. -/
  def momentHankel (m : ℕ → ℝ) (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
    fun i j => m (i.1 + j.1)

  def principalHankelDeterminant (m : ℕ → ℝ) (r : ℕ) : ℝ :=
    Matrix.det (momentHankel m r)

  /-- The squared Vandermonde factor for the squared nodes indexed by `I`. -/
  def squaredVandermonde (x : Fin 3 → ℝ) (I : Finset (Fin 3)) : ℝ :=
    ∏ p ∈ (I.product I).filter (fun p => p.1 < p.2),
      (x p.2 ^ 2 - x p.1 ^ 2) ^ 2

  def weightedSquaredVandermonde (w x : Fin 3 → ℝ) (I : Finset (Fin 3)) : ℝ :=
    (∏ j ∈ I, w j) * squaredVandermonde x I

  /-- Andreief/Cauchy--Binet expansion and positivity through rank three. -/
  def rawThreeAtomMomentConePositivity : Prop :=
    ∀ (w x : Fin 3 → ℝ),
      (∀ j : Fin 3, 0 < w j) →
      (∀ j : Fin 3, 0 < x j) →
      (∀ i j : Fin 3, i ≠ j → x i ≠ x j) →
      let m := threeAtomMoment w x
      (∀ r : ℕ, 1 ≤ r → r ≤ 3 →
        principalHankelDeterminant m r =
          ∑ I ∈ (Finset.univ : Finset (Finset (Fin 3))).filter
            (fun I => I.card = r),
            weightedSquaredVandermonde w x I) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ 3 →
        ∀ I : Finset (Fin 3), I.card = r →
          0 < weightedSquaredVandermonde w x I) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ 3 →
        0 < principalHankelDeterminant m r)

  /-- The alternating power column in the compact Gram matrix. -/
  def compactGramColumn (x : ℝ) (a : Fin N → ℝ) (n : ℕ) (j : Fin N) : Fin n → ℝ :=
    fun i => (-1 : ℝ) ^ (i : ℕ) * (x + a j)⁻¹ ^ ((i : ℕ) + 1)

  def compactGramMatrix (x : ℝ) (a : Fin N → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
    fun i k => 2 * ∑ j : Fin N, compactGramColumn x a n j i * compactGramColumn x a n j k

  /-- The Vandermonde factor on a finite index set. -/
  def finiteVandermonde {N : ℕ} (a : Fin N → ℝ) (I : Finset (Fin N)) : ℝ :=
    ∏ p ∈ (I.product I).filter (fun p => p.1 < p.2),
      (a p.2 - a p.1)

  /-- The elementary symmetric polynomial of reciprocal shifted nodes in `J`. -/
  def reciprocalElementarySymmetric {N : ℕ} (x : ℝ) (a : Fin N → ℝ)
      (J : Finset (Fin N)) (k : ℕ) : ℝ :=
    ∑ K ∈ J.powerset.filter (fun K => K.card = k),
      ∏ j ∈ K, (x + a j)⁻¹

  def principalMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
      (S : Finset (Fin n)) : ℝ :=
    Matrix.det (fun i j : S => A i.1 j.1)

  /-- The sum of principal minors of a fixed cardinality. -/
  def matrixElementarySymmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
      (r : ℕ) : ℝ :=
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = r),
      principalMinor A S

  /-- The least Rayleigh quotient, i.e. the smallest eigenvalue for a real symmetric matrix. -/
  def realLeastEigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
    sInf {q : ℝ | ∃ v : Fin n → ℝ,
      (∑ i : Fin n, (v i) ^ 2 = 1) ∧
      q = ∑ i : Fin n, ∑ j : Fin n, v i * A i j * v j}

  def realPositiveDefinite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ i j : Fin n, A i j = A j i) ∧
    (∀ v : Fin n → ℝ, v ≠ 0 →
      0 < ∑ i : Fin n, ∑ j : Fin n, v i * A i j * v j)

  /-- Compact Gram determinant, principal elementary-symmetric formula, and eigenvalue bound. -/
  def exactCompactGramFormulas : Prop :=
    ∀ (N n : ℕ) (x : ℝ) (a : Fin N → ℝ),
      0 < n →
      n ≤ N →
      (∀ j : Fin N, x + a j ≠ 0) →
      let A := compactGramMatrix x a n
      (Matrix.det A =
        2 ^ n *
          ∑ I ∈ (Finset.univ : Finset (Finset (Fin N))).filter
            (fun I => I.card = n),
            (finiteVandermonde a I) ^ 2 /
              (∏ i ∈ I, (x + a i) ^ (2 * n))) ∧
      (matrixElementarySymmetric A (n - 1) =
        2 ^ (n - 1) *
          ∑ J ∈ (Finset.univ : Finset (Finset (Fin N))).filter
            (fun J => J.card = n - 1),
            (finiteVandermonde a J) ^ 2 /
              (∏ j ∈ J, (x + a j) ^ (2 * (n - 1))) *
                (∑ k ∈ Finset.range n,
                  (reciprocalElementarySymmetric x a J k) ^ 2)) ∧
      (realPositiveDefinite A →
        realLeastEigenvalue A ≥
          Matrix.det A / matrixElementarySymmetric A (n - 1))

end

end MathlibPlus.Open.ResearchFormalization
