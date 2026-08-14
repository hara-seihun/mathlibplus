import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

private def zeroPadded {L : ℕ} (z : Fin L → ℂ) (j : ℕ) : ℂ :=
  if h : j < L then z ⟨j, h⟩ else 0

private def fejerWindow {n : ℕ} (z : Fin (2 * n - 1) → ℂ)
    (r : Fin ((2 * n - 1) + (n - 1) - 1)) : ℂ :=
  let L := 2 * n - 1
  let H := n - 1
  ∑ j : Fin H,
    if H ≤ r.1 + 1 + j.1 then
      zeroPadded z (r.1 + 1 + j.1 - H)
    else 0

private noncomputable def fejerCost (n : ℕ) (z : Fin (2 * n - 1) → ℂ) : ℝ :=
  let L := 2 * n - 1
  let H := n - 1
  ((L + H - 1 : ℕ) : ℝ) / (H : ℝ) ^ 2 *
    ∑ r : Fin (L + H - 1), ‖fejerWindow z r‖ ^ 2

private def totalMass {L : ℕ} (z : Fin L → ℂ) : ℂ :=
  ∑ j : Fin L, z j

private noncomputable def threeCombLift (n : ℕ) (z : Fin (2 * n - 1) → ℂ) (E : ℂ)
    (j : Fin (2 * n - 1)) : ℂ :=
  z j +
    if j.1 = 0 ∨ j.1 = n - 1 ∨ j.1 = 2 * n - 2 then E / 3 else 0

private def threeCombCount (n : ℕ)
    (r : Fin ((2 * n - 1) + (n - 1) - 1)) : ℕ :=
  let H := n - 1
  ∑ j : Fin H,
    if H ≤ r.1 + 1 + j.1 ∧
        (r.1 + 1 + j.1 - H = 0 ∨
          r.1 + 1 + j.1 - H = n - 1 ∨
          r.1 + 1 + j.1 - H = 2 * n - 2) then 1 else 0

/-- Claim 43630: with the displayed zero padding and the `1,n,2n-1`
three-comb, every one of the `3H` windows contains one spike and the exact
Fejér identity, including its nonnegative slack, holds. -/
def exactThreeCombFejerIdentity : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (z : Fin (2 * n - 1) → ℂ) (E : ℂ),
      (∀ r : Fin ((2 * n - 1) + (n - 1) - 1),
        threeCombCount n r = 1) ∧
      fejerCost n (threeCombLift n z E) =
        ‖totalMass z + E‖ ^ 2 +
          (fejerCost n z - ‖totalMass z‖ ^ 2) ∧
      0 ≤ fejerCost n z - ‖totalMass z‖ ^ 2

end MathlibPlus.Open.Analysis
