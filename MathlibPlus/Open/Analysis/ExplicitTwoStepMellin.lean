import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

/-!
Closed registry node for the explicit two-step Mellin source.  The source's
complex power, Mellin integral, removable continuation, and completion are
kept as explicit interfaces; no analytic zero theorem is asserted here.
-/

/-- Claim 3737: the source `1_[1,2] - 1_[2,3]` has the displayed Mellin
transform, a removable continuation at zero, and the stated completed factor. -/
noncomputable def explicitTwoStepMellinTransform : Prop :=
  let q : ℝ → ℂ := fun x =>
    Set.indicator (Set.Icc (1 : ℝ) 2) (fun _ => 1) x -
      Set.indicator (Set.Icc (2 : ℝ) 3) (fun _ => 1) x
  let M : ℂ → ℂ := fun s =>
    ∫ x : ℝ, q x * Complex.cpow (x : ℂ) (s - 1)
  let A : ℂ → ℂ := fun s =>
    (1 / 2) * s * (s - 1) * Complex.cpow (Real.pi : ℂ) (-s / 2) *
      Complex.Gamma (s / 2)
  let E : ℂ → ℂ := fun s =>
    (1 / 2) * (M s / A s + M (1 - s) / A (1 - s))
  (∫ x : ℝ, q x) = 0 ∧
    (∃ M₀ : ℂ → ℂ,
      ContinuousAt M₀ 0 ∧ ∀ s : ℂ, s ≠ 0 → M₀ s = M s) ∧
    (∀ s : ℂ, s ≠ 0 →
      M s =
        (2 * Complex.cpow (2 : ℂ) s - Complex.cpow (3 : ℂ) s - 1) / s) ∧
    (∀ s : ℂ,
      E s = (1 / 2) * (M s / A s + M (1 - s) / A (1 - s)))

end MathlibPlus.Open.Analysis
