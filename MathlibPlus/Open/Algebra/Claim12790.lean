import MathlibPlus.Basic

namespace MathlibPlus.Open.Algebra

/-- Statement-fidelity registry node for claim 12790.  The displayed
polynomial and displayed root formulas are retained literally; in particular,
this node does not silently repair the apparent coefficient/root mismatch. -/
def reciprocalGenusOneCounterfeit12790 : Prop :=
  let P : ℝ → ℝ := fun u => 1 + 7 * u + 9 * u ^ 2
  let α : ℝ := (-7 + Real.sqrt 13) / 2
  let β : ℝ := (-7 - Real.sqrt 13) / 2
  (∀ u : ℝ, u ≠ 0 →
      P u = 9 * u ^ 2 * P (1 / (9 * u))) ∧
    (∀ u : ℝ, P u = 0 ↔ u = α ∨ u = β) ∧
    P α = 0 ∧ P β = 0 ∧ α * β = 9 ∧
    |α| < 2 ∧ |β| < 6 ∧ |α| / 3 ≠ |β| / 3

end MathlibPlus.Open.Algebra
