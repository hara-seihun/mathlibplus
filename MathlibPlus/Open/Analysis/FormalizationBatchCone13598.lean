import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis.FormalizationBatchCone13598

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

noncomputable def coneLaplaceKernel {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  Complex.exp (-(Complex.ofReal (Complex.re (Matrix.trace (A * B)))) )

noncomputable def claim_13598 : Prop :=
  ∀ (g : ℝ → ℝ)
    (μ : ∀ m : ℕ, Measure (Matrix (Fin m) (Fin m) ℂ)),
    (∀ m : ℕ,
      (μ m) Set.univ = 1 ∧
        (μ m) {B | positiveHermitian m B} = (μ m) Set.univ ∧
        ∀ A : Matrix (Fin m) (Fin m) ℂ,
          positiveHermitian m A →
            MeasureTheory.integral (μ m) (fun B => coneLaplaceKernel A B) =
              Matrix.det (cfc g A)) →
      (∀ m : ℕ, ∀ U : Matrix (Fin m) (Fin m) ℂ,
        unitaryMatrix m U →
          Measure.map (conjugateMatrix U) (μ m) = μ m ∧
            (∀ A : Matrix (Fin m) (Fin m) ℂ,
              positiveHermitian m A →
                Matrix.det (cfc g (conjugateMatrix U A)) =
                  Matrix.det (cfc g A)))

end MathlibPlus.Open.Analysis.FormalizationBatchCone13598
