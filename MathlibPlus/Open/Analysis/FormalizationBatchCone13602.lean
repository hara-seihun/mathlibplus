import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis.FormalizationBatchCone13602

noncomputable instance matrixMeasurableSpace (m : ℕ) :
    MeasurableSpace (Matrix (Fin m) (Fin m) ℂ) := borel _

def positiveHermitian (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  A.IsHermitian ∧
    ∀ v : Fin m → ℂ,
      0 ≤ Complex.re (∑ i, star (v i) * (A.mulVec v) i)

def conjugateMatrix {m : ℕ} (U B : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  U * B * Matrix.conjTranspose U

def unitaryMatrix (m : ℕ) (U : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  U * Matrix.conjTranspose U = 1 ∧
    Matrix.conjTranspose U * U = 1

noncomputable def diagonalMeasure {m : ℕ}
    (μ : Measure (Matrix (Fin m) (Fin m) ℂ)) : Measure (Fin m → ℝ) :=
  Measure.map (fun B i => Complex.re (B i i)) μ

def leadingCorner {r m : ℕ} (h : r ≤ m)
    (B : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => B (Fin.castLE h i) (Fin.castLE h j)

noncomputable def claim_13602 : Prop :=
  ∀ (g : ℝ → ℝ)
    (μ : ∀ m : ℕ, Measure (Matrix (Fin m) (Fin m) ℂ)),
    (∀ m : ℕ,
      (μ m) Set.univ = 1 ∧
        (μ m) {B | positiveHermitian m B} = (μ m) Set.univ) →
    (∀ r m : ℕ, ∀ h : r ≤ m,
      Measure.map (leadingCorner h) (μ m) = μ r) →
    (∀ m : ℕ, ∀ U : Matrix (Fin m) (Fin m) ℂ,
      unitaryMatrix m U →
        Measure.map (conjugateMatrix U) (μ m) = μ m) →
    (let ν : Measure ℝ :=
      Measure.map
        (fun B : Matrix (Fin 1) (Fin 1) ℂ =>
          Complex.re (B (0 : Fin 1) (0 : Fin 1)))
        (μ 1)
     (∀ m : ℕ, diagonalMeasure (μ m) =
       Measure.pi (fun _ : Fin m => ν)) ∧
     (∀ a : ℝ, 0 ≤ a →
       MeasureTheory.integral ν (fun b =>
         Complex.exp (-(Complex.ofReal (a * b)))) =
           Complex.ofReal (g a))) →
    ∃ (ι : Type*) (hι : Countable ι) (x : ι → ℝ) (c : ℝ),
      letI := hι
      0 ≤ c ∧
        (∀ k, 0 < x k) ∧
        Summable x ∧
        (∀ a : ℝ, 0 ≤ a →
          g a = Real.exp (-c * a) * ∏' k, (1 + x k * a)⁻¹)

end MathlibPlus.Open.Analysis.FormalizationBatchCone13602
