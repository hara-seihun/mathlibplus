import Mathlib
import MathlibPlus.Open.Analysis.ReflectionCovariantDyadicProduct

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Whole-row twisting by the fixed dyadic factor sends the even scalar
channel into the odd coordinate on the critical line. -/
def claim13465 : Prop :=
  ∀ (S : ℂ → ℝ) (ZPlus ZMinus : ℂ → ℂ),
    (∀ s : ℂ, S (1 - s) = S s) →
    (∀ s : ℂ, ZPlus (1 - s) = ZMinus s) →
    (∀ s : ℂ, ZMinus (1 - s) = ZPlus s) →
    ∀ t : ℝ,
      let s : ℂ := (1 : ℂ) / 2 + (t : ℂ) * Complex.I
      let θ : ℝ := t * Real.log 2
      let dₑ : ℝ := Real.cos θ / Real.sqrt 2
      let dₒ : ℝ := -Real.sin θ / Real.sqrt 2
      let RPlus : ℂ → ℂ := fun u => (S u : ℂ) - 2 * ZPlus u
      let RMinus : ℂ → ℂ := fun u => (S u : ℂ) - 2 * ZMinus u
      (dyadicPlus s).re = dₑ ∧
        (dyadicPlus s).im = dₒ ∧
        (dyadicPlus s * RPlus s).im =
          dₒ * S s - 2 * (dₑ * (ZPlus s).im + dₒ * (ZPlus s).re) ∧
        (dₒ * S s ≠ 0 ↔ Real.sin θ ≠ 0 ∧ S s ≠ 0) ∧
        RPlus (1 - s) = RMinus s ∧
        RMinus (1 - s) = RPlus s

end

end MathlibPlus.Open.Analysis
