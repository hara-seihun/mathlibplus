import Mathlib

open scoped BigOperators Topology
open Filter

namespace MathlibPlus.Open.Research

/-- The power sum of a finite list of coordinates. -/
def powerSum (K : Type u) [Semiring K] {j : ℕ} (x : Fin j → K) (n : ℕ) : K :=
  ∑ i, x i ^ n

/-- The origin is the only common zero of the consecutive power sums. -/
def originOnlyCommonPowerSumZero (K : Type u) [Field K] [CharZero K] (j d : ℕ) : Prop :=
  ∀ x : Fin j → K,
    (∀ i : Fin j, powerSum K x (d + 1 + i.1) = 0) →
      ∀ i : Fin j, x i = 0

/-- Concatenate two square matrices horizontally. -/
def concatenatedMatrix {K : Type u} [Semiring K] {r : ℕ}
    (A V : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin (r + r)) K :=
  fun i c =>
    if h : c.1 < r then
      A i ⟨c.1, h⟩
    else
      V i ⟨c.1 - r, by omega⟩

/-- The increasing column set used in the generalized Cramer formula. -/
def selectedConcatColumns {r : ℕ} (I J : Finset (Fin r)) : Finset (Fin (r + r)) :=
  (Finset.univ \ I).image (Fin.castAdd r) ∪ J.image (Fin.natAdd r)

/-- The increasing embedding of a finite subset into its ambient ordered finite type. -/
def orderedFinsetEmbedding {r k : ℕ} (I : Finset (Fin r)) (hI : I.card = k) : Fin k → Fin r :=
  fun a => ((Finset.orderIsoOfFin I hI a : I) : Fin r)

/-- Generalized Cramer's minor formula with one-based signs and increasing columns. -/
def generalizedCramerMinorFormula (K : Type u) [Field K] : Prop :=
  ∀ (r k : ℕ) (A V : Matrix (Fin r) (Fin r) K)
    (I J : Finset (Fin r)) (hI : I.card = k) (hJ : J.card = k),
    Matrix.det A ≠ 0 →
      let X : Matrix (Fin r) (Fin r) K := A⁻¹ * V
      ∀ c : Fin r → Fin (r + r),
        StrictMono c →
        Finset.univ.image c = selectedConcatColumns I J →
          Matrix.det (X.submatrix (orderedFinsetEmbedding I hI)
              (orderedFinsetEmbedding J hJ)) =
            (-1 : K) ^
                (k * r - Nat.choose k 2 - ∑ i ∈ I, (i.1 + 1)) *
              (Matrix.det ((concatenatedMatrix A V).submatrix id c) /
                Matrix.det A)

/-- The Cayley identities relating the compression and feedback matrices. -/
def cayleyRelationBetweenCompressionAndFeedback
    (K : Type u) [Field K] [CharZero K] : Prop :=
  ∀ (r : ℕ) (H : Matrix (Fin r) (Fin r) K),
    Matrix.det (1 + H) ≠ 0 →
      let C : Matrix (Fin r) (Fin r) K := H * (1 + H)⁻¹
      C = 1 - (1 + H)⁻¹ ∧
        1 - (2 : K) • C = (1 - H) * (1 + H)⁻¹ ∧
        ((C - (2 : K)⁻¹ • (1 : Matrix (Fin r) (Fin r) K)).det = 0 ↔
          (H - (1 : Matrix (Fin r) (Fin r) K)).det = 0)

/-- Perron criteria for the positive folded determinant. -/
def perronSufficientCriterionForFoldedSign : Prop :=
  ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, 0 ≤ C i j) →
      (spectralRadius ℝ C < ENNReal.ofReal (1 / 2 : ℝ) →
          0 < (1 - (2 : ℝ) • C).det) ∧
      ((spectralRadius ℝ C < ENNReal.ofReal (1 / 2)) ↔
        ∃ h : Fin n → ℝ,
          (∀ i, 0 < h i) ∧
            ∀ i, (2 : ℝ) * (Matrix.mulVec C h) i < h i) ∧
      (∀ H : Matrix (Fin n) (Fin n) ℝ,
        (∀ i j, 0 ≤ H i j) →
          (spectralRadius ℝ H < ENNReal.ofReal (1 : ℝ) →
              0 < (1 - H).det) ∧
          ((∃ h : Fin n → ℝ,
              (∀ i, 0 < h i) ∧ ∀ i, (Matrix.mulVec H h) i < h i) →
            0 < (1 - H).det))

/-- Nonzero conjugation-invariant unit-phase sums have zero mean, positive
mean square, and positive and negative subsequences. -/
def zeroMeanNonzeroMeanSquareTrigonometricOscillation (L : ℕ) : Prop :=
  0 < L →
    ∀ (ω C : Fin L → ℂ),
      (Function.Injective ω) ∧
      (∀ ν, ‖ω ν‖ = 1) ∧
      (∀ ν, ω ν ≠ 1) ∧
      (∀ ν, C ν ≠ 0) ∧
      (∃ σ : Equiv.Perm (Fin L),
        Function.Involutive σ ∧
        (∀ ν, ω (σ ν) = star (ω ν)) ∧
        (∀ ν, C (σ ν) = star (C ν))) →
      let T : ℕ → ℂ := fun n => ∑ ν, C ν * (ω ν) ^ n
      (∀ n, (T n).im = 0) ∧
      Tendsto
        (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, T n)
        atTop (𝓝 0) ∧
      Tendsto
        (fun N : ℕ =>
          (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, Complex.normSq (T n))
        atTop (𝓝 (∑ ν, Complex.normSq (C ν))) ∧
      0 < ∑ ν, Complex.normSq (C ν) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ N : ℕ,
          (∃ n : ℕ, N ≤ n ∧ ε ≤ (T n).re) ∧
          (∃ n : ℕ, N ≤ n ∧ (T n).re ≤ -ε)

end MathlibPlus.Open.Research
