import MathlibPlus.Open.ResearchFormalization.Batch.Analysis
import MathlibPlus.Open.ResearchFormalization.C0226Claim3301
import MathlibPlus.Open.AdmittedBatch.Products

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.C0226

open MathlibPlus.Open.ResearchFormalization.Batch

noncomputable def complexLeastEigenvalue {n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {q : ℝ | ∃ v : Fin n → ℂ,
    (∑ j : Fin n, ‖v j‖ ^ 2 = 1) ∧
      q = (∑ i : Fin n, ∑ j : Fin n,
        star (v i) * K i j * v j).re}

def separationSineRatio (a : ℝ) : ℝ :=
  if a = 0 then 1 else Real.pi * a / Real.sinh (Real.pi * a)

def interpolationSineRatio (a : ℝ) : ℝ :=
  if a = 0 then 1 else Real.sinh (Real.pi * a) / (Real.pi * a)

def inverseEulerProduct (a : ℝ) : ℝ :=
  ∏' m : {m : ℕ // 0 < m},
    (1 + a ^ 2 / (m.1 : ℝ) ^ 2)⁻¹

/-- Claim 3302: the minimum-eigenvalue trace bound for the normalized Cauchy Gram. -/
def claim3302 (n : ℕ) (y t : Fin n → ℝ) : Prop :=
  (∀ j, 0 < y j) →
    Function.Injective (fun j : Fin n => halfPlaneParameter (y j) (t j)) →
      0 < n →
        let s : Fin n → ℂ := fun j => halfPlaneParameter (y j) (t j)
        ∃ δstar : ℝ,
          (∀ j, δstar ≤ separationProduct s j) ∧
            (∃ j, δstar = separationProduct s j) ∧
              let K : Matrix (Fin n) (Fin n) ℂ := fun j k =>
                ((2 : ℂ) * Real.sqrt (y j * y k)) /
                  (s j + star (s k))
              complexLeastEigenvalue K ≥
                  (∑ j : Fin n, (separationProduct s j)⁻¹ ^ (2 : ℕ))⁻¹ ∧
                (∑ j : Fin n, (separationProduct s j)⁻¹ ^ (2 : ℕ))⁻¹ ≥
                  δstar ^ 2 / (n : ℝ)

/-- Claim 3306: the cardinality-free lower bound for every train separation product. -/
def claim3306 (n : ℕ) (y t : Fin (n + 1) → ℝ)
    (Y d L : ℝ) : Prop :=
  0 < Y → 0 < d → 0 < L →
    (∀ j, 0 < y j ∧ y j ≤ Y) →
      (∀ j : Fin n,
        t (Fin.succ j) - t (Fin.castSucc j) ≥ d / L) →
        let s : Fin (n + 1) → ℂ := fun j => halfPlaneParameter (y j) (t j)
        let a : ℝ := 2 * Y * L / d
        (∀ j, separationProduct s j ≥ inverseEulerProduct a) ∧
          (∀ j, separationProduct s j ≥ separationSineRatio a) ∧
            inverseEulerProduct a = separationSineRatio a

abbrev HalfLineL2 :=
  MeasureTheory.Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
abbrev HalfLineEvaluationData (n : ℕ) := EuclideanSpace ℂ (Fin n)

def normalizedEvaluationCoordinate (n : ℕ) (y t : Fin n → ℝ)
    (f : HalfLineL2) (j : Fin n) : ℂ :=
  ∫ x : ℝ,
    star (halfLineLaplaceKernel (y j) (t j) x) * f x
      ∂(volume.restrict (Ioi (0 : ℝ)))

def isNormalizedEvaluationOperator (n : ℕ) (y t : Fin n → ℝ)
    (T : HalfLineL2 →L[ℂ] HalfLineEvaluationData n) : Prop :=
  ∀ (f : HalfLineL2) (j : Fin n),
    (T f) j = normalizedEvaluationCoordinate n y t f j

def isHalfLineRightInverse (n : ℕ) (T : HalfLineL2 →L[ℂ] HalfLineEvaluationData n)
    (R : HalfLineEvaluationData n →L[ℂ] HalfLineL2) : Prop :=
  ∀ z : HalfLineEvaluationData n, T (R z) = z

/-- Claim 3308: the minimum-norm right inverse has the stated cost. -/
def claim3308 : Prop :=
  ∀ (n : ℕ) (y t : Fin (n + 1) → ℝ) (Y d L : ℝ),
    0 < Y → 0 < d → 0 < L →
    (∀ j, 0 < y j ∧ y j ≤ Y) →
      (∀ j : Fin n,
        t (Fin.succ j) - t (Fin.castSucc j) ≥ d / L) →
        let a : ℝ := 2 * Y * L / d
        ∃ T : HalfLineL2 →L[ℂ] HalfLineEvaluationData (n + 1),
          isNormalizedEvaluationOperator (n + 1) y t T ∧
            ∃ R : HalfLineEvaluationData (n + 1) →L[ℂ] HalfLineL2,
              isHalfLineRightInverse (n + 1) T R ∧
                (∀ R' : HalfLineEvaluationData (n + 1) →L[ℂ] HalfLineL2,
                  isHalfLineRightInverse (n + 1) T R' → ‖R‖ ≤ ‖R'‖) ∧
                ‖R‖ ≤ Real.sqrt (n + 1 : ℝ) * interpolationSineRatio a ∧
                  Real.sqrt (n + 1 : ℝ) * interpolationSineRatio a ≤
                    Real.sqrt (n + 1 : ℝ) *
                      Real.exp (2 * Real.pi * Y * L / d)

end MathlibPlus.Open.ResearchFormalization.C0226
