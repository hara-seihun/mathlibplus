import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators
open Set MeasureTheory

/-- A real, even, compactly supported smooth source with the exact-S0 conditions. -/
def exactS0Source (q : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : WithTop ℕ∞) q ∧
    HasCompactSupport q ∧
    (∀ x : ℝ, q (-x) = q x) ∧
    q 0 = 0 ∧
    (∫ x : ℝ, q x) = 0

/-- The arithmetic sample sum, extended as the same `tsum` expression to all real inputs. -/
noncomputable def sampleSum (q : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑' n : ℕ, q (((n + 1 : ℕ) : ℝ) * v)

/-- Smoothness on the positive half-line, eventual vanishing, and a smooth flat extension at zero. -/
def smoothCompactFlatSampleSum (q : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : WithTop ℕ∞) (sampleSum q) (Ioi 0) ∧
    (∃ R : ℝ, ∀ v : ℝ, R ≤ v → sampleSum q v = 0) ∧
    (∃ extension : ℝ → ℝ,
      (∀ v : ℝ, 0 < v → extension v = sampleSum q v) ∧
        ContDiff ℝ (⊤ : WithTop ℕ∞) extension ∧
          (∀ k : ℕ, iteratedDeriv k extension 0 = 0))

/-- The Mellin integrand of the sample sum at a complex parameter. -/
noncomputable def sampleSumMellinIntegrand
    (q : ℝ → ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  (sampleSum q v : ℂ) * Complex.cpow (v : ℂ) (s - 1)

/-- The Mellin integral of the sample sum over the positive half-line. -/
noncomputable def sampleSumMellin (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ v in Ioi (0 : ℝ), sampleSumMellinIntegrand q s v

/-- Smoothness, compact support at infinity, and flatness at zero make the sample-sum
Mellin transform converge for every complex parameter and define an entire function. -/
def entireMellinTransformOfSampleSum : Prop :=
  ∀ q : ℝ → ℝ,
    exactS0Source q →
      smoothCompactFlatSampleSum q →
        (∀ s : ℂ,
          IntegrableOn (sampleSumMellinIntegrand q s) (Ioi (0 : ℝ))) ∧
          Differentiable ℂ (sampleSumMellin q)

end MathlibPlus.Open.Analysis
