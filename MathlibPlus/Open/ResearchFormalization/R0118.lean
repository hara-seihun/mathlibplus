import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open MeasureTheory

/-- Claim 18077: strict Chebyshevness on the ordered cell transversals. -/
def strictChebyshevOnCellTransversals
    {α : Type*} (f : ℕ → α → ℝ) (C : ℕ → Set α) : Prop :=
  ∀ (r : ℕ) (n j : Fin r → ℕ) (y : Fin r → α),
    StrictMono n →
    StrictMono j →
    (∀ i : Fin r, y i ∈ C (n i)) →
    0 < Matrix.det (fun i k : Fin r => f (j k) (y i))

/-- The operative nonzero condition for Claim 18078. -/
def positiveNonzeroCellMeasures
    {α : Type*} [MeasurableSpace α]
    (μ : ℕ → Measure α) (C : ℕ → Set α) : Prop :=
  ∀ n : ℕ, 0 < μ n (C n)

/-- Finiteness of the cell moments and finite rowwise products mentioned in
Claim 18078. -/
def cellMomentsAndRowProductsIntegrable
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (C : ℕ → Set α) (μ : ℕ → Measure α) : Prop :=
  ∀ (n r : ℕ) (j : Fin r → ℕ),
    (0 < r) →
    IntegrableOn (fun x => ∏ k : Fin r, f (j k) x) (C n) (μ n)

/-- The cell-integral matrix in Claim 18079. -/
noncomputable def arithmeticTransversalCellIntegral
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (C : ℕ → Set α) (μ : ℕ → Measure α)
    (n j : ℕ) : ℝ :=
  ∫ x in C n, f j x ∂μ n

/-- Claim 18079: arithmetic-transversal integration yields a strictly totally
positive cell-integral matrix. -/
def arithmeticTransversalIntegrationStrictlyTotallyPositive
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (C : ℕ → Set α) (μ : ℕ → Measure α) : Prop :=
  strictChebyshevOnCellTransversals f C →
  positiveNonzeroCellMeasures μ C →
  cellMomentsAndRowProductsIntegrable f C μ →
  ∀ (r : ℕ) (n j : Fin r → ℕ),
    StrictMono n →
    StrictMono j →
    0 < Matrix.det
      (fun i k : Fin r => arithmeticTransversalCellIntegral f C μ (n i) (j k))

end MathlibPlus.Open.ResearchFormalization
