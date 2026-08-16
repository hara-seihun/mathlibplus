import Mathlib

namespace MathlibPlus.Open.Research

/-- Exact arithmetic identity at the target values from claim 60303. -/
def claim60303 : Prop :=
  let L : ℝ := (1529 : ℝ) / 10000
  let t : ℝ := (2097 : ℝ) / 20000
  let y : ℝ := (31 : ℝ) / 100
  let N : ℕ := 690988
  N = 690988 ∧
    t + y ^ 2 / 2 = (2097 : ℝ) / 20000 + (961 : ℝ) / 20000 ∧
      (2097 : ℝ) / 20000 + (961 : ℝ) / 20000 = L

/-- The displayed target point is strictly inside the stated strip from claim 60304. -/
def claim60304 : Prop :=
  let t : ℝ := (2097 : ℝ) / 20000
  let y : ℝ := (31 : ℝ) / 100
  y ^ 2 = (961 : ℝ) / 10000 ∧
    y ^ 2 < (7903 : ℝ) / 10000 ∧
      (7903 : ℝ) / 10000 = 1 - 2 * t

end MathlibPlus.Open.Research
