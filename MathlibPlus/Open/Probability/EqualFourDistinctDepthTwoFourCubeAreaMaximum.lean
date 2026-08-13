import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Field

namespace MathlibPlus.Open.Probability

/--
On the uniform four-coordinate Boolean cube, the exact maximum optimal
posterior-variance area of the equal mixture of four distinct Boolean
functions represented by depth-at-most-two decision trees is `41 / 32`.

A policy is encoded by its first three fresh adaptive queries. Querying the
unique fourth coordinate afterward makes every target measurable, and any
earlier measurability contributes zero conditional variance. Thus `PolicyArea`
is exactly the cumulative area, including the prior variance.
-/
def equalFourDistinctDepthTwoFourCubeAreaMaximum : Prop :=
  let Ω := Fin 4 → Bool
  let sgn : Bool → ℚ := fun b => if b then 1 else -1
  let Branch : Fin 4 → Type := fun r =>
    Bool ⊕ ({j : Fin 4 // j ≠ r} × Bool)
  let Tree := Σ r : Fin 4, Branch r × Branch r
  let evalBranch : (r : Fin 4) → Branch r → Ω → ℚ := fun _ b x =>
    match b with
    | Sum.inl c => sgn c
    | Sum.inr p => sgn p.2 * sgn (x p.1.1)
  let evalTree : Tree → Ω → ℚ := fun t x =>
    if x t.1 then evalBranch t.1 t.2.2 x else evalBranch t.1 t.2.1 x
  let Distinct : (Fin 4 → Tree) → Prop := fun trees =>
    ∀ i j : Fin 4, i ≠ j → evalTree (trees i) ≠ evalTree (trees j)
  let Fresh : Fin 4 → (Bool → Fin 4) → (Bool → Bool → Fin 4) → Prop :=
    fun q0 q1 q2 =>
      (∀ a, q1 a ≠ q0) ∧
        ∀ a b, q2 a b ≠ q0 ∧ q2 a b ≠ q1 a
  let PolicyArea : (Ω → ℚ) → Fin 4 → (Bool → Fin 4) →
      (Bool → Bool → Fin 4) → ℚ := fun g q0 q1 q2 =>
    let mean0 := (∑ x : Ω, g x) / 16
    let var0 := (∑ x : Ω, (g x) ^ 2) / 16 - mean0 ^ 2
    let mean1 := fun a : Bool =>
      (∑ x : Ω, if x q0 = a then g x else 0) / 8
    let var1 := fun a : Bool =>
      (∑ x : Ω, if x q0 = a then (g x) ^ 2 else 0) / 8 - (mean1 a) ^ 2
    let mean2 := fun a b : Bool =>
      (∑ x : Ω, if x q0 = a ∧ x (q1 a) = b then g x else 0) / 4
    let var2 := fun a b : Bool =>
      (∑ x : Ω, if x q0 = a ∧ x (q1 a) = b then (g x) ^ 2 else 0) / 4 -
        (mean2 a b) ^ 2
    let mean3 := fun a b c : Bool =>
      (∑ x : Ω,
        if x q0 = a ∧ x (q1 a) = b ∧ x (q2 a b) = c then g x else 0) / 2
    let var3 := fun a b c : Bool =>
      (∑ x : Ω,
        if x q0 = a ∧ x (q1 a) = b ∧ x (q2 a b) = c then (g x) ^ 2 else 0) / 2 -
        (mean3 a b c) ^ 2
    var0 + (∑ a : Bool, var1 a) / 2 +
      (∑ a : Bool, ∑ b : Bool, var2 a b) / 4 +
      (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, var3 a b c) / 8
  let target : (Fin 4 → Tree) → Ω → ℚ := fun trees x =>
    (∑ i : Fin 4, evalTree (trees i) x) / 4
  (∀ trees : Fin 4 → Tree, Distinct trees →
      ∃ q0 q1 q2, Fresh q0 q1 q2 ∧
        PolicyArea (target trees) q0 q1 q2 ≤ 41 / 32) ∧
    ∃ trees : Fin 4 → Tree, Distinct trees ∧
      ∀ q0 q1 q2, Fresh q0 q1 q2 →
        41 / 32 ≤ PolicyArea (target trees) q0 q1 q2

end MathlibPlus.Open.Probability
