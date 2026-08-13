import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Field

namespace MathlibPlus.Open.Probability

/--
An explicit continuous four-component depth-two family on the uniform
four-coordinate Boolean cube has the displayed exact piecewise-quadratic
optimal posterior-variance area.  The prior variance is included.
-/
def explicitFourDepthTwoAreaCurve : Prop :=
  let Ω := Fin 4 → Bool
  let sgn : Bool → ℚ := fun b => if b then 1 else -1
  let T0 : Ω → ℚ := fun x => if x 1 then sgn (x 2) else sgn (x 3)
  let T1 : Ω → ℚ := fun x => if x 2 then sgn (x 1) else sgn (x 3)
  let T2 : Ω → ℚ := fun x => if x 1 then sgn (x 2) else sgn (x 0)
  let T3 : Ω → ℚ := fun x => sgn (x 1) * sgn (x 2)
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
  let ExactArea : (Ω → ℚ) → ℚ → Prop := fun g value =>
    (∃ q0 q1 q2, Fresh q0 q1 q2 ∧ PolicyArea g q0 q1 q2 ≤ value) ∧
      ∀ q0 q1 q2, Fresh q0 q1 q2 → value ≤ PolicyArea g q0 q1 q2
  let target : ℚ → Ω → ℚ := fun t x =>
    (1 - 3 * t) * T0 x + t * (T1 x + T2 x + T3 x)
  let value : ℚ → ℚ := fun t =>
    if t ≤ 1 / 5 then 2 - 6 * t + (53 / 4) * t ^ 2
    else if t ≤ 1 / 4 then 9 / 4 - (15 / 2) * t + (29 / 2) * t ^ 2
    else 5 / 2 - 9 * t + (33 / 2) * t ^ 2
  T0 ≠ T1 ∧ T0 ≠ T2 ∧ T0 ≠ T3 ∧ T1 ≠ T2 ∧ T1 ≠ T3 ∧ T2 ≠ T3 ∧
    ∀ t : ℚ, 0 ≤ t → t ≤ 1 / 3 → ExactArea (target t) (value t)

end MathlibPlus.Open.Probability
