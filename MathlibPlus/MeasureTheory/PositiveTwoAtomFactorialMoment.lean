import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory

namespace MathlibPlus.MeasureTheory.PositiveTwoAtomFactorialMoment

noncomputable section

/-- The moments of the positive two-atom measure from claim 12541. -/
theorem moment_formula (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    let μ : Measure ℝ :=
      Measure.dirac (1 : ℝ) +
        ENNReal.ofReal ε • Measure.dirac ((1 : ℝ) / 4)
    (∫ x : ℝ, x ^ j ∂μ) = 1 + ε * ((1 : ℝ) / 4) ^ j := by
  dsimp
  let f : ℝ → ℝ := fun x => x ^ j
  have hf₁ : Integrable f (Measure.dirac (1 : ℝ)) := by
    exact MeasureTheory.integrable_dirac (by simp)
  have hf₄ : Integrable f (Measure.dirac ((1 : ℝ) / 4)) := by
    exact MeasureTheory.integrable_dirac (by simp)
  have hscaled :
      Integrable f (ENNReal.ofReal ε • Measure.dirac ((1 : ℝ) / 4)) := by
    exact hf₄.smul_measure (by simp)
  change
    (∫ x, f x ∂(Measure.dirac (1 : ℝ) +
      ENNReal.ofReal ε • Measure.dirac ((1 : ℝ) / 4))) = _
  rw [MeasureTheory.integral_add_measure hf₁ hscaled]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
  simp [f, ENNReal.toReal_ofReal (le_of_lt hε)]

/-- The factorial-scaled moment formula in the same model. -/
theorem factorial_scaled_moment_formula (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    let μ : Measure ℝ :=
      Measure.dirac (1 : ℝ) +
        ENNReal.ofReal ε • Measure.dirac ((1 : ℝ) / 4)
    let m : ℕ → ℝ := fun k => ∫ x : ℝ, x ^ k ∂μ
    let h : ℕ → ℝ := fun k => m k / (Nat.factorial (2 * k) : ℝ)
    m j = 1 + ε * ((1 : ℝ) / 4) ^ j ∧
      h j = (1 + ε * ((1 : ℝ) / 4) ^ j) / (Nat.factorial (2 * j) : ℝ) := by
  dsimp
  constructor
  · exact moment_formula ε hε j
  · rw [moment_formula ε hε j]

end

end MathlibPlus.MeasureTheory.PositiveTwoAtomFactorialMoment
