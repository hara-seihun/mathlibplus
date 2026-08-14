import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.Analysis.DensityIntervalBatch

def symmetricDensityPoint (A : Set ℝ) (x : ℝ) : Prop :=
  Filter.Tendsto
    (fun r : ℝ =>
      (volume (A ∩ Set.Icc (x - r) (x + r))).toReal /
        (volume (Set.Icc (x - r) (x + r))).toReal)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

def chebyshevT : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | k + 2, x => 2 * x * chebyshevT (k + 1) x - chebyshevT k x

def densityFactor (n : ℕ) : ℝ :=
  chebyshevT (n - 1)
    (((1 : ℝ) + ((n : ℝ)⁻¹) ^ 4) /
      (1 - ((n : ℝ)⁻¹) ^ 4))

def claim_51835 : Prop :=
  ∀ (A : Set ℝ) (xstar : ℝ) (Lambda : ℕ → ℝ → ℝ) (B : ℕ → ℝ),
    volume A > 0 →
    symmetricDensityPoint A xstar →
    (∀ n : ℕ, ∀ᵐ x ∂(volume.restrict A), Lambda n x ≤ B n) →
    (∀ n : ℕ, 2 ≤ n →
      ∃ l u : ℝ,
        l < u ∧ xstar ∈ Set.Icc l u ∧
        (volume (A ∩ Set.Icc l u)).toReal /
            (volume (Set.Icc l u)).toReal ≥
          1 - ((n : ℝ)⁻¹) ^ 4 ∧
        sSup (Lambda n '' Set.Icc l u) ≤ densityFactor n * B n) ∧
    (∀ n : ℕ, 2 ≤ n →
      ((1 : ℝ) + ((n : ℝ)⁻¹) ^ 4) /
          (1 - ((n : ℝ)⁻¹) ^ 4) =
        Real.cosh (2 * Real.artanh (((n : ℝ)⁻¹) ^ 2))) ∧
    (∀ (d : ℕ) (u : ℝ),
      chebyshevT d (Real.cosh u) = Real.cosh ((d : ℝ) * u)) ∧
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => densityFactor n - 1)
      (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)

end MathlibPlus.Open.Analysis.DensityIntervalBatch

end
