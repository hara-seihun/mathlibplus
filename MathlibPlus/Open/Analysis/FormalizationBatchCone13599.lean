import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis.FormalizationBatchCone13599

noncomputable instance matrixMeasurableSpace (m : ℕ) :
    MeasurableSpace (Matrix (Fin m) (Fin m) ℂ) := borel _

def positiveHermitian (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  A.IsHermitian ∧
    ∀ v : Fin m → ℂ,
      0 ≤ Complex.re (∑ i, star (v i) * (A.mulVec v) i)

noncomputable def coneLaplaceKernel {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  Complex.exp (-(Complex.ofReal (Complex.re (Matrix.trace (A * B)))) )

noncomputable def diagonalMeasure {m : ℕ}
    (μ : Measure (Matrix (Fin m) (Fin m) ℂ)) : Measure (Fin m → ℝ) :=
  Measure.map (fun B i => Complex.re (B i i)) μ

noncomputable def claim_13599 : Prop :=
  ∀ (g : ℝ → ℝ)
    (μ : ∀ m : ℕ, Measure (Matrix (Fin m) (Fin m) ℂ)),
    (∀ m : ℕ,
      (μ m) Set.univ = 1 ∧
        (μ m) {B | positiveHermitian m B} = (μ m) Set.univ ∧
        ∀ A : Matrix (Fin m) (Fin m) ℂ,
          positiveHermitian m A →
            MeasureTheory.integral (μ m) (fun B => coneLaplaceKernel A B) =
              Matrix.det (cfc g A)) →
      (∀ m : ℕ, ∀ a : Fin m → ℝ,
        (∀ j, 0 ≤ a j) →
          MeasureTheory.integral (μ m) (fun B =>
            Complex.exp
              (-(Complex.ofReal (∑ j, a j * Complex.re (B j j))))) =
            Complex.ofReal (∏ j, g (a j))) ∧
        (let ν : Measure ℝ :=
          Measure.map
            (fun B : Matrix (Fin 1) (Fin 1) ℂ =>
              Complex.re (B (0 : Fin 1) (0 : Fin 1)))
            (μ 1)
         ν Set.univ = 1 ∧
         (∀ a : ℝ, 0 ≤ a →
           MeasureTheory.integral ν (fun b =>
             Complex.exp (-(Complex.ofReal (a * b)))) =
               Complex.ofReal (g a)) ∧
         (∀ m : ℕ, diagonalMeasure (μ m) =
           Measure.pi (fun _ : Fin m => ν)))

end MathlibPlus.Open.Analysis.FormalizationBatchCone13599
