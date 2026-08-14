import Mathlib

<<<<<<< ours
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
=======
namespace MathlibPlus.Open.Research.FormalizationBatch019ffedb

open MeasureTheory
noncomputable section

/-! Exact source-side definitions used by the admitted de Branges identity. -/

def SuperExponentialRealSource (Φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, Φ (-t) = Φ t) ∧
    ∀ A : ℝ, 0 < A →
      Integrable (fun t : ℝ => Real.exp (A * |t|) * |Φ t|) volume

def sourceXi (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (Φ t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))

def sourceC (Φ : ℝ → ℝ) (y : ℝ) (sigma : ℂ) : ℂ :=
  ∫ d : ℝ,
    (Φ (y + d) : ℂ) * (Φ (y - d) : ℂ) *
      Complex.exp (Complex.I * sigma * (d : ℂ))

def sourceE (Φ : ℝ → ℝ) (ω : ℝ) (z : ℂ) : ℂ :=
  sourceXi Φ (z + Complex.I * (ω : ℂ))

def sourceESharp (Φ : ℝ → ℝ) (ω : ℝ) (z : ℂ) : ℂ :=
  star (sourceE Φ ω (star z))

def sourceEDeriv (Φ : ℝ → ℝ) (ω : ℝ) (z : ℂ) : ℂ :=
  deriv (sourceE Φ ω) z

def sourceESharpDeriv (Φ : ℝ → ℝ) (ω : ℝ) (z : ℂ) : ℂ :=
  deriv (sourceESharp Φ ω) z

def sourceDelta (w z : ℂ) : ℂ := z - star w

def sourceSigma (w z : ℂ) : ℂ := z + star w

/-- The removable value of `sin (δ y) / δ` at `δ = 0`. -/
def sourceSinQuot (δ : ℂ) (y : ℝ) : ℂ :=
  if δ = 0 then (y : ℂ) else Complex.sin (δ * (y : ℂ)) / δ

def sourceDeBrangesKernel (Φ : ℝ → ℝ) (ω : ℝ) (w z : ℂ) : ℂ :=
  if z = star w then
    (sourceESharpDeriv Φ ω z * star (sourceESharp Φ ω w) -
      sourceEDeriv Φ ω z * star (sourceE Φ ω w)) /
      (2 * (Real.pi : ℂ) * Complex.I)
  else
    (sourceE Φ ω z * star (sourceE Φ ω w) -
      sourceESharp Φ ω z * star (sourceESharp Φ ω w)) /
      (2 * (Real.pi : ℂ) * Complex.I * (star w - z))

def sourceDeBrangesIntegral (Φ : ℝ → ℝ) (ω : ℝ) (w z : ℂ) : ℂ :=
  (4 / (Real.pi : ℂ)) *
    ∫ y in Set.Ici (0 : ℝ),
      sourceSinQuot (sourceDelta w z) y *
        (Real.sinh (2 * ω * y) : ℂ) *
        sourceC Φ y (sourceSigma w z)

/-- Claim 7577: the exact source integral, including its diagonal removable value. -/
def exactDeBrangesSourceIntegral7577 : Prop :=
  ∀ (Φ : ℝ → ℝ), SuperExponentialRealSource Φ →
    ∀ (ω : ℝ) (w z : ℂ),
      sourceDeBrangesKernel Φ ω w z = sourceDeBrangesIntegral Φ ω w z

/-- The standard positive-real-argument integral defining the modified Bessel K. -/
def modifiedBesselK (ν : ℂ) (β : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Complex.exp (-(β : ℂ) * (Real.cosh t : ℂ)) *
      Complex.cosh (ν * (t : ℂ))

/-- Claim 7593: every zero in the order variable of `K_{i τ}(β)` is real. -/
def realityOfBesselKZeros7593 : Prop :=
  ∀ (β : ℝ), 0 < β →
    ∀ (τ : ℂ), modifiedBesselK (Complex.I * τ) β = 0 → τ.im = 0

def gaussianBesselSource (c t : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * Real.cosh (9 * t / 2) -
      6 * Real.pi * c * Real.cosh (5 * t / 2)) *
    Real.exp (-2 * Real.pi * Real.cosh (2 * t))

def gaussianBesselTransform (c : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (gaussianBesselSource c t : ℂ) *
    Complex.exp (Complex.I * z * (t : ℂ))

def gaussianBesselClosedForm (c : ℝ) (z : ℂ) : ℂ :=
  2 * (Real.pi : ℂ) ^ 2 *
      (modifiedBesselK ((Complex.I * z + (9 / 2 : ℂ)) / 2) (2 * Real.pi) +
        modifiedBesselK ((Complex.I * z - (9 / 2 : ℂ)) / 2) (2 * Real.pi)) -
    3 * (Real.pi : ℂ) * (c : ℂ) *
      (modifiedBesselK ((Complex.I * z + (5 / 2 : ℂ)) / 2) (2 * Real.pi) +
        modifiedBesselK ((Complex.I * z - (5 / 2 : ℂ)) / 2) (2 * Real.pi))

/-- Claim 7597: the explicit transform of the solvable `c`-dial source. -/
def solvableCDialTransform7597 : Prop :=
  ∀ (c : ℝ) (z : ℂ),
    gaussianBesselTransform c z = gaussianBesselClosedForm c z

end
end MathlibPlus.Open.Research.FormalizationBatch019ffedb
>>>>>>> theirs
