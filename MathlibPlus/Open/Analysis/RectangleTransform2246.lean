import Mathlib

namespace MathlibPlus.Open.Analysis

open Set

/-- The certified rectangle in the `z` coordinate from claim 2244. -/
def certifiedZRectangle_claim2246 : Set ℂ :=
  {z | |z.re| ≤ (130 : ℝ) ∧ |z.im| ≤ (4 : ℝ) / 25}

/-- The exact rectangle obtained in the physical `t` coordinate. -/
def physicalTRectangle_claim2246 : Set ℂ :=
  {t |
    |t.re| ≤ 260 * Real.pi / Real.log 8 ∧
      |t.im| ≤ 8 * Real.pi / (25 * Real.log 8)}

/-- Claim 2246: multiplication by `2π/log 8` sends the certified `z`
rectangle exactly to the displayed physical-variable rectangle. -/
def physicalVariableRectangle_claim2246 : Prop :=
  let scale : ℂ := (2 * Real.pi / Real.log 8 : ℝ)
  {t : ℂ | ∃ z ∈ certifiedZRectangle_claim2246,
      t = scale * z} = physicalTRectangle_claim2246

end MathlibPlus.Open.Analysis
