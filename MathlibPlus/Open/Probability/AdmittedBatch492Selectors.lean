import Mathlib

namespace MathlibPlus.Open.Probability.AdmittedBatch492Selectors

open scoped BigOperators

noncomputable section

private abbrev Ω4 := Fin 4 → Bool

private def sign4 (x : Ω4) (i : Fin 4) : ℚ :=
  if x i then 1 else -1

private def selectorA (x : Ω4) : ℚ :=
  if x (1 : Fin 4) then sign4 x 3 else -sign4 x 2

private def selectorB (x : Ω4) : ℚ :=
  sign4 x 0 * sign4 x 2

private def selectorMixture (x : Ω4) : ℚ :=
  (21 / 22 : ℚ) * selectorA x + (1 / 22 : ℚ) * selectorB x

private def walsh4 (f : Ω4 → ℚ) (S : Finset (Fin 4)) : ℚ :=
  (∑ x : Ω4,
      f x * ∏ i : Fin 4, if i ∈ S then sign4 x i else 1) / (16 : ℚ)

private def reducedDepthTwoDisplay (f : Ω4 → ℚ) (root : Fin 4)
    (child : Bool → Fin 4) : Prop :=
  (∀ b, child b ≠ root) ∧
    ∀ x : Ω4,
      f x = if x root then -sign4 x (child true) else -sign4 x (child false)

/-- Claim 49277: the two displayed selectors and their common global levels. -/
def claim49277 : Prop :=
  let globalLevel : Fin 4 → ℕ := fun i => if i.val < 2 then 1 else 2
  let policyA : Ω4 → List (Fin 4) := fun x =>
    [1, if x (1 : Fin 4) then 3 else 2]
  let policyB : Ω4 → List (Fin 4) := fun _ => [0, 2]
  (∀ x : Ω4,
      selectorMixture x =
        (21 / 22 : ℚ) *
            (if x (1 : Fin 4) then sign4 x 3 else -sign4 x 2) +
          (1 / 22 : ℚ) * (sign4 x 0 * sign4 x 2)) ∧
    (∀ x : Ω4,
      policyA x = [1, if x (1 : Fin 4) then 3 else 2] ∧
        policyB x = [0, 2]) ∧
    globalLevel 0 = 1 ∧ globalLevel 1 = 1 ∧
      globalLevel 2 = 2 ∧ globalLevel 3 = 2

/-- Claim 49278: the complete nonzero Fourier support of the mixture. -/
def claim49278 : Prop :=
  let μ : Ω4 → ℚ := selectorMixture
  let c : Finset (Fin 4) → ℚ := walsh4 μ
  let y0 : Finset (Fin 4) := {2}
  let y1 : Finset (Fin 4) := {3}
  let x1y0 : Finset (Fin 4) := {1, 2}
  let x1y1 : Finset (Fin 4) := {1, 3}
  let x0y0 : Finset (Fin 4) := {0, 2}
  (c y0 = -21 / 44) ∧
    (c y1 = 21 / 44) ∧
    (c x1y0 = 21 / 44) ∧
    (c x1y1 = 21 / 44) ∧
    (c x0y0 = 1 / 22) ∧
    (∀ S : Finset (Fin 4),
      c S ≠ 0 ↔ S = y0 ∨ S = y1 ∨ S = x1y0 ∨ S = x1y1 ∨ S = x0y0)

/-- Claim 49315: aligned level-two displays with a shared global level map. -/
def claim49315 : Prop :=
  let H : Ω4 → ℚ := fun x =>
    if x (0 : Fin 4) then -sign4 x 3 else -sign4 x 2
  let K : Ω4 → ℚ := fun x =>
    if x (1 : Fin 4) then -sign4 x 3 else -sign4 x 2
  let level : Fin 4 → ℕ := fun i => if i.val < 2 then 1 else 2
  (reducedDepthTwoDisplay H 0 (fun b => if b then 3 else 2)) ∧
    (reducedDepthTwoDisplay K 1 (fun b => if b then 3 else 2)) ∧
    level 0 = 1 ∧ level 1 = 1 ∧ level 2 = 2 ∧ level 3 = 2

end

end MathlibPlus.Open.Probability.AdmittedBatch492Selectors
