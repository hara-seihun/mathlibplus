import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Field

namespace MathlibPlus.Open.Probability

/--
Exact near-sharp five-component depth-two family on the four-sign cube.
The coefficient `M` is the positive integer weight of the parity component;
the four displayed branch components have weight one each.  This is a
statement-only registry node: no proof belongs in `MathlibPlus.Open`.
-/
def weightedFiveComponentNearSharpDepthTwoArea : Prop :=
  let Ω := Fin 4 → Bool
  let sgn : Bool → ℚ := fun b => if b then 1 else -1
  let parity : Ω → ℚ := fun x => sgn (x 0) * sgn (x 2)
  let branchA : Ω → ℚ := fun x => if x 1 then sgn (x 0) else sgn (x 2)
  let branchB : Ω → ℚ := fun x => if x 2 then sgn (x 0) else sgn (x 1)
  let branchC : Ω → ℚ := fun x => if x 0 then sgn (x 2) else -1
  let branchD : Ω → ℚ := fun x => if x 0 then 1 else -sgn (x 2)
  let Fresh : Fin 4 → (Bool → Fin 4) →
      (Bool → Bool → Fin 4) →
      (Bool → Bool → Bool → Fin 4) → Prop :=
    fun q0 q1 q2 q3 =>
      (∀ a, q1 a ≠ q0) ∧
      (∀ a b, q2 a b ≠ q0 ∧ q2 a b ≠ q1 a) ∧
      ∀ a b c,
        q3 a b c ≠ q0 ∧ q3 a b c ≠ q1 a ∧ q3 a b c ≠ q2 a b
  let PolicyArea : (Ω → ℚ) → Fin 4 → (Bool → Fin 4) →
      (Bool → Bool → Fin 4) →
      (Bool → Bool → Bool → Fin 4) → ℚ :=
    fun g q0 q1 q2 q3 =>
      let mean0 := (∑ x : Ω, g x) / 16
      let var0 := (∑ x : Ω, (g x) ^ 2) / 16 - mean0 ^ 2
      let mean1 := fun a : Bool =>
        (∑ x : Ω, if x q0 = a then g x else 0) / 8
      let var1 := fun a : Bool =>
        (∑ x : Ω, if x q0 = a then (g x) ^ 2 else 0) / 8 -
          (mean1 a) ^ 2
      let mean2 := fun a b : Bool =>
        (∑ x : Ω,
          if x q0 = a ∧ x (q1 a) = b then g x else 0) / 4
      let var2 := fun a b : Bool =>
        (∑ x : Ω,
          if x q0 = a ∧ x (q1 a) = b then (g x) ^ 2 else 0) / 4 -
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
  ∀ M : ℕ, 1 ≤ M →
    let W : ℚ := (M : ℚ) + 4
    let g : Ω → ℚ := fun x =>
      ((M : ℚ) * parity x + branchA x + branchB x + branchC x + branchD x) / W
    let q0 : Fin 4 := 0
    let q1 : Bool → Fin 4 := fun _ => 2
    let q2 : Bool → Bool → Fin 4 := fun _ _ => 1
    let q3 : Bool → Bool → Bool → Fin 4 := fun _ _ _ => 3
    Fresh q0 q1 q2 q3 ∧
      PolicyArea g q0 q1 q2 q3 =
        (4 * (M : ℚ) ^ 2 + 12 * (M : ℚ) + 27) /
          (2 * W ^ 2) ∧
      (∀ r0 r1 r2 r3, Fresh r0 r1 r2 r3 →
        PolicyArea g r0 r1 r2 r3 ≥
          (4 * (M : ℚ) ^ 2 + 12 * (M : ℚ) + 27) /
            (2 * W ^ 2))

end MathlibPlus.Open.Probability
