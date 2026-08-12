import Mathlib

/-!
# Sharp subsequential asymptotics for the raised K-type selector

This file formalizes admitted claim 307 (`C-0019`) as an open registry node.
The least selector is characterized inside the proposition so that its dependence
on the fixed positive weight `k` is explicit.
-/

open Filter Set Topology
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.KTypeSelector

noncomputable section

/-- Claim 307: along every phase-locked sequence with phase strictly inside the
first bad window, the least safe K-type has the stated sharp square-root
asymptotic.  The one-sided phase limit records the displayed worst-phase
constant, and the final clause is the source's quantitative lower bound at
phase `π / 4` for every safe selector (not only the least one). -/
def sharpSubsequentialAsymptotics : Prop :=
  let xPlus : ℝ := (34 + 12 * Real.sqrt 6) / 73
  let xMinus : ℝ := (34 - 12 * Real.sqrt 6) / 73
  let δ₀ : ℝ := Real.arccos (Real.sqrt xPlus)
  let δ₁ : ℝ := Real.arccos (Real.sqrt xMinus)
  Tendsto (fun φ : ℝ => Real.sqrt ((φ - δ₀) / 2))
      (nhdsWithin δ₁ (Iio δ₁))
      (𝓝 (Real.sqrt ((δ₁ - δ₀) / 2))) ∧
    ∀ k : ℝ, 0 < k →
      let A : ℕ → ℝ := fun r => k + 2 * (r : ℝ) + 1 / 2
      let B : ℕ → ℝ := fun r => k + 2 * (r : ℝ) + 3 / 2
      let ψ : ℕ → ℝ → ℝ := fun m t =>
        ∑ r ∈ Finset.range m,
          (Real.arctan (t / A r) + Real.arctan (t / B r))
      let Θ : ℕ → ℝ → ℝ := fun m t => t * Real.log 2 + ψ m t
      let q : ℝ → ℝ := fun x => 73 * x ^ 2 - 68 * x + 4
      let Safe : ℝ → ℕ → Prop := fun t m => 0 ≤ q ((Real.cos (Θ m t)) ^ 2)
      ∃ mStar : ℝ → ℕ,
        (∀ t : ℝ,
          Safe t (mStar t) ∧
            ∀ m : ℕ, Safe t m → mStar t ≤ m) ∧
        (∀ φ : ℝ, φ ∈ Ioo δ₀ δ₁ →
          let tSeq : ℕ → ℝ := fun n =>
            ((n : ℝ) * Real.pi + φ) / Real.log 2
          Tendsto
            (fun n : ℕ => (mStar (tSeq n) : ℝ) / Real.sqrt (tSeq n))
            atTop
            (𝓝 (Real.sqrt ((φ - δ₀) / 2)))) ∧
        (let tSeq : ℕ → ℝ := fun n =>
            ((n : ℝ) * Real.pi + Real.pi / 4) / Real.log 2
          ∀ (n m : ℕ), Safe (tSeq n) m →
            ((m : ℝ) * (k + (m : ℝ)) ≥
              ((Real.pi / 4 - δ₀) / 2) * tSeq n))

end

end MathlibPlus.Open.Analysis.KTypeSelector
