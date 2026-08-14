import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.K0100

/-- A moment sequence with the even/odd square-root lift used by the claims. -/
def liftedMoment (μ : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then μ (k / 2) else 0

def hankel (μ : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => μ (i.1 + j.1)

def shiftedHankel (μ : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => μ (i.1 + j.1 + 1)

def liftedHamburger (μ : ℕ → ℝ) (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  hankel (liftedMoment μ) (2 * n)

def positiveDefinite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ v : Fin n → ℝ, v ≠ 0 →
    0 < ∑ i, v i * ∑ j, M i j * v j

def evenIndex (n : ℕ) (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.1, by omega⟩

def oddIndex (n : ℕ) (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.1 + 1, by omega⟩

def parityIndex (n : ℕ) : Sum (Fin n) (Fin n) → Fin (2 * n)
  | Sum.inl i => evenIndex n i
  | Sum.inr i => oddIndex n i

def reorderedHamburger (μ : ℕ → ℝ) (n : ℕ) :
    Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) ℝ :=
  fun i j => liftedHamburger μ n (parityIndex n i) (parityIndex n j)

def claim8504 : Prop :=
  ∀ (μ : ℕ → ℝ) (n : ℕ),
    hankel μ n = (fun i j => μ (i.1 + j.1)) ∧
    shiftedHankel μ n = (fun i j => μ (i.1 + j.1 + 1))

def claim8506 : Prop :=
  ∀ (μ : ℕ → ℝ) (n : ℕ),
    Function.Bijective (parityIndex n) ∧
    reorderedHamburger μ n =
      Matrix.fromBlocks (hankel μ n)
        (0 : Matrix (Fin n) (Fin n) ℝ)
        (0 : Matrix (Fin n) (Fin n) ℝ)
        (shiftedHankel μ n)

def claim8507 : Prop :=
  ∀ (μ : ℕ → ℝ) (n : ℕ),
    positiveDefinite (liftedHamburger μ n) ↔
      positiveDefinite (hankel μ n) ∧ positiveDefinite (shiftedHankel μ n)

def claim8508 : Prop :=
  ∀ (μ : ℕ → ℝ) (n : ℕ),
    Matrix.det (liftedHamburger μ n) =
      Matrix.det (hankel μ n) * Matrix.det (shiftedHankel μ n)

def represents (μ : ℕ → ℝ) (ρ : Measure ℝ) : Prop :=
  ∀ k : ℕ,
    Integrable (fun x : ℝ => x ^ k) ρ ∧
      (∫ x : ℝ, x ^ k ∂ρ) = μ k

def representsStieltjes (μ : ℕ → ℝ) (ρ : Measure ℝ) : Prop :=
  represents μ ρ ∧ ρ (Set.Iio 0) = 0

def squareRootLift (ρ : Measure ℝ) : Measure ℝ :=
  (1 / 2 : ENNReal) •
    (Measure.map Real.sqrt ρ + Measure.map (fun x : ℝ => -Real.sqrt x) ρ)

def claim8509 : Prop :=
  ∀ (μ : ℕ → ℝ) (ρ : Measure ℝ),
    representsStieltjes μ ρ →
      (∀ f : ℝ → ℝ,
        Measurable f →
        Integrable (fun x : ℝ => f (Real.sqrt x)) ρ →
        Integrable (fun x : ℝ => f (-Real.sqrt x)) ρ →
        MeasureTheory.integral (squareRootLift ρ) f =
          (1 / 2 : ℝ) *
            ((∫ x : ℝ, f (Real.sqrt x) ∂ρ) +
              (∫ x : ℝ, f (-Real.sqrt x) ∂ρ))) ∧
      represents (liftedMoment μ) (squareRootLift ρ)

def jacobiMatrix (n : ℕ) (d b : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i.1 = j.1 then d i.1
    else if i.1 + 1 = j.1 then b j.1
    else if j.1 + 1 = i.1 then b i.1
    else 0

def lowerBidiagonal (n : ℕ) (r s : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i.1 = j.1 then r i.1
    else if j.1 + 1 = i.1 then s i.1
    else 0

def claim8511 : Prop :=
  ∀ (n : ℕ) (d b : ℕ → ℝ),
    positiveDefinite (jacobiMatrix n d b) →
    (∀ k : ℕ, 1 ≤ k → k < n → 0 < b k) →
      ∃ r s : ℕ → ℝ,
        (∀ k : ℕ, k < n → 0 < r k) ∧
        (∀ k : ℕ, 1 ≤ k → k < n → 0 < s k) ∧
        jacobiMatrix n d b =
          lowerBidiagonal n r s * (lowerBidiagonal n r s).transpose

def zeroDiagonalLift {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) ℝ :=
  Matrix.fromBlocks
    (0 : Matrix (Fin n) (Fin n) ℝ) L L.transpose
    (0 : Matrix (Fin n) (Fin n) ℝ)

def interlaceIndex (n : ℕ) (k : Fin (2 * n)) : Sum (Fin n) (Fin n) :=
  if k.1 % 2 = 0 then
    Sum.inl ⟨k.1 / 2, by omega⟩
  else
    Sum.inr ⟨k.1 / 2, by omega⟩

def interlacedMatrix {n : ℕ}
    (M : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun i j => M (interlaceIndex n i) (interlaceIndex n j)

def interlacedOffDiagonal (r s : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then r (k / 2) else s ((k + 1) / 2)

def zeroDiagonalJacobi (N : ℕ) (c : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i.1 + 1 = j.1 then c i.1
    else if j.1 + 1 = i.1 then c j.1
    else 0

def claim8512 : Prop :=
  ∀ (n : ℕ) (r s : ℕ → ℝ),
    (∀ k : ℕ, k < n → 0 < r k) ∧
    (∀ k : ℕ, 1 ≤ k → k < n → 0 < s k) →
      Function.Bijective (interlaceIndex n) ∧
      interlacedMatrix (zeroDiagonalLift (lowerBidiagonal n r s)) =
        zeroDiagonalJacobi (2 * n) (interlacedOffDiagonal r s)

def realInner {α : Type} [Fintype α] (v w : α → ℝ) : ℝ :=
  ∑ i, v i * w i

def vectorNorm {α : Type} [Fintype α] (v : α → ℝ) : ℝ :=
  Real.sqrt (realInner v v)

def sumVector {n : ℕ} (v w : Fin n → ℝ) : Sum (Fin n) (Fin n) → ℝ
  | Sum.inl i => v i
  | Sum.inr i => w i

def liftedEigenvector {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (x τ : ℝ) : Sum (Fin n) (Fin n) → ℝ :=
  (Real.sqrt 2)⁻¹ •
    sumVector v
      (τ • ((Real.sqrt x)⁻¹ • L.transpose.mulVec v))

def claim8515 : Prop :=
  ∀ (n : ℕ) (J L : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (x τ : ℝ),
    J = L * L.transpose →
    J.mulVec v = x • v →
    0 < x →
    vectorNorm v = 1 →
    (τ = 1 ∨ τ = -1) →
      vectorNorm (liftedEigenvector L v x τ) = 1 ∧
      (zeroDiagonalLift L).mulVec (liftedEigenvector L v x τ) =
        (τ * Real.sqrt x) • liftedEigenvector L v x τ

def eigenvalueSet {α : Type} [Fintype α]
    (M : Matrix α α ℝ) : Set ℝ :=
  {x | ∃ v : α → ℝ, v ≠ 0 ∧ M.mulVec v = x • v}

def claim8516 : Prop :=
  ∀ (n : ℕ) (J L : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ),
    J = L * L.transpose →
    (∀ i : Fin n, 0 < x i) →
    StrictMono x →
    eigenvalueSet J = Set.range x →
      eigenvalueSet (zeroDiagonalLift L) =
        {y | ∃ i : Fin n, y = Real.sqrt (x i) ∨ y = -Real.sqrt (x i)} ∧
      (∀ y : ℝ,
        Matrix.det
            (y • (1 : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) ℝ) -
              zeroDiagonalLift L) =
          Matrix.det (y ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) - J))

def basisVector {n : ℕ} (k : Fin n) : Fin n → ℝ :=
  fun i => if i = k then 1 else 0

def gaussianWeight {α : Type} (v : α → ℝ) (k : α) : ℝ :=
  (v k) ^ 2

def firstIndex (n : ℕ) (h : 0 < n) : Fin n :=
  ⟨0, h⟩

def lastIndex (n : ℕ) (h : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

def claim8517 : Prop :=
  ∀ (n : ℕ) (h : 0 < n) (J L : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (x : ℝ),
    J = L * L.transpose →
    J.mulVec v = x • v →
    0 < x →
    vectorNorm v = 1 →
      ∀ τ : ℝ, τ = 1 ∨ τ = -1 →
        gaussianWeight (liftedEigenvector L v x τ) (Sum.inl (firstIndex n h)) =
          gaussianWeight v (firstIndex n h) / 2

def claim8519 : Prop :=
  ∀ (n : ℕ) (h : 0 < n) (J L : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (x : ℝ),
    J = L * L.transpose →
    J.mulVec v = x • v →
    0 < x →
    vectorNorm v = 1 →
      ∀ τ : ℝ, τ = 1 ∨ τ = -1 →
        gaussianWeight (liftedEigenvector L v x τ) (Sum.inl (lastIndex n h)) =
          gaussianWeight v (lastIndex n h) / 2

end MathlibPlus.Open.ResearchFormalization.K0100
