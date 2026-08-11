import Mathlib

/-!
# Rank-two moment-coordinate sharpness at `R = 7/15`

This registry node formalizes admitted claim 164. The two-atom measure
`δ₁ + u δ_L` is represented by its exact moments `m_j = 1 + u L^j`; no
extra measure-theoretic hypotheses are inserted. The last conjunct makes the
claim's phrase "no smaller constant is sufficient using only `S ≥ 1`" an
explicit quantified family of negative-chamber witnesses.
-/

open Filter
open scoped Topology

namespace MathlibPlus.Open.MomentGeometry

/-- The family `δ₁ + u δ_L` approaches the sharp rank-two boundary
`R = 7/15` from within the negative chamber while retaining `S ≥ 1`. -/
def rankTwoSharpnessAtR : Prop :=
  let moment : ℝ → ℝ → ℕ → ℝ := fun u L j => 1 + u * L ^ j
  let R : ℝ → ℝ → ℝ := fun u L =>
    moment u L 1 ^ 2 / (moment u L 0 * moment u L 2)
  let S : ℝ → ℝ → ℝ := fun u L =>
    moment u L 1 * moment u L 3 / moment u L 2 ^ 2
  let Q : ℝ → ℝ → ℝ := fun u L => 3 * S u L + 15 * R u L - 10
  (∀ u : ℝ, 0 < u →
    Tendsto (R u) atTop (𝓝 (u / (1 + u))) ∧
    Tendsto (S u) atTop (𝓝 1) ∧
    Tendsto (Q u) atTop (𝓝 (15 * u / (1 + u) - 7)) ∧
    (u < 7 / 8 → ∀ᶠ L : ℝ in atTop, 1 < L ∧ 1 ≤ S u L ∧ Q u L < 0)) ∧
  Tendsto (fun u : ℝ => u / (1 + u)) (𝓝[<] (7 / 8 : ℝ)) (𝓝 (7 / 15 : ℝ)) ∧
  (∀ C : ℝ, C < 7 / 15 →
    ∃ u : ℝ, 0 < u ∧ u < 7 / 8 ∧
      ∀ᶠ L : ℝ in atTop, 1 < L ∧ C < R u L ∧ 1 ≤ S u L ∧ Q u L < 0)

end MathlibPlus.Open.MomentGeometry
