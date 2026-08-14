import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- A real, even, compactly supported smooth source with the exact-S0 conditions. -/
def exactS0Source (q : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ q ∧
    Function.Even q ∧
    HasCompactSupport q ∧
    q 0 = 0 ∧
    (∫ x, q x) = 0

/-- The arithmetic dilation sum from an exact-S0 source. -/
def arithmeticSampleSum (q : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑' n : ℕ, q (((n + 1 : ℕ) : ℝ) * v)

/-- The Mellin transform of the arithmetic dilation sum. -/
def sampleSumMellinTransform (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ v in Set.Ioi (0 : ℝ),
    (arithmeticSampleSum q v : ℂ) * Complex.cpow (v : ℂ) (s - 1)

/-- The Mellin transform of a source. -/
def sourceMellinTransform (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (q x : ℂ) * Complex.cpow (x : ℂ) (s - 1)

/-- The critical strip in the complex plane. -/
def criticalStrip : Set ℂ :=
  {s | 0 < s.re ∧ s.re < 1}

/--
Zeta--Mellin factorization for every exact-S0 source, together with the
holomorphy of its Mellin transform in the critical strip.
-/
def zetaMellinFactorizationClaim3644 : Prop :=
  ∀ (q : ℝ → ℝ),
    exactS0Source q →
      ((∀ s : ℂ, 1 < s.re →
          sampleSumMellinTransform q s =
            riemannZeta s * sourceMellinTransform q s) ∧
        DifferentiableOn ℂ (sourceMellinTransform q) criticalStrip)

end MathlibPlus.Open.Analysis
