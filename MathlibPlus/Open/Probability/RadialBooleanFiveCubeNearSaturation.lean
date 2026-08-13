import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Field

/-
Exact n=5 near-saturation witness for the radial Boolean-direction route.
Statement only: no proof belongs in MathlibPlus.Open.
-/
namespace MathlibPlus.Open.Probability

/--
An explicit Boolean direction on the five-sign cube has optimal fresh-query
area `577 / 256` and maximum correlation `15 / 16` with a depth-at-most-two
Boolean tree.  Its radial necessary-condition product is
`(577 / 256) * (15 / 16)^2 = 129825 / 65536 < 2`.
-/
def radialBooleanFiveCubeNearSaturation : Prop :=
  let Ω := Fin 5 → Bool
  let sgn : Bool → ℚ := fun b => if b then 1 else -1
  let Branch : Fin 5 → Type := fun r =>
    Bool ⊕ ({j : Fin 5 // j ≠ r} × Bool)
  let Tree := Σ r : Fin 5, Branch r × Branch r
  let evalBranch : (r : Fin 5) → Branch r → Ω → ℚ := fun _ b x =>
    match b with
    | Sum.inl c => sgn c
    | Sum.inr p => sgn p.2 * sgn (x p.1.1)
  let evalTree : Tree → Ω → ℚ := fun t x =>
    if x t.1 then evalBranch t.1 t.2.2 x else evalBranch t.1 t.2.1 x
  let U : Ω → ℚ := fun x =>
    if x 4 then
      if x 2 then
        if x 3 ∧ x 1 ∧ ¬x 0 then 1 else -1
      else if x 3 then -1 else 1
    else if x 3 ∨ ¬x 2 then 1 else -1
  let correlation : Tree → ℚ := fun t =>
    (∑ x : Ω, U x * evalTree t x) / 32
  let Fresh : Fin 5 → (Bool → Fin 5) →
      (Bool → Bool → Fin 5) → (Bool → Bool → Bool → Fin 5) →
      (Bool → Bool → Bool → Bool → Fin 5) → Prop :=
    fun q0 q1 q2 q3 q4 =>
      (∀ a, q1 a ≠ q0) ∧
      (∀ a b, q2 a b ≠ q0 ∧ q2 a b ≠ q1 a) ∧
      (∀ a b c, q3 a b c ≠ q0 ∧ q3 a b c ≠ q1 a ∧ q3 a b c ≠ q2 a b) ∧
      ∀ a b c d,
        q4 a b c d ≠ q0 ∧ q4 a b c d ≠ q1 a ∧
        q4 a b c d ≠ q2 a b ∧ q4 a b c d ≠ q3 a b c
  let PolicyArea : (Ω → ℚ) → Fin 5 → (Bool → Fin 5) →
      (Bool → Bool → Fin 5) → (Bool → Bool → Bool → Fin 5) →
      (Bool → Bool → Bool → Bool → Fin 5) → ℚ :=
    fun g q0 q1 q2 q3 q4 =>
      let mean0 := (∑ x : Ω, g x) / 32
      let var0 := (∑ x : Ω, (g x) ^ 2) / 32 - mean0 ^ 2
      let mean1 := fun a : Bool =>
        (∑ x : Ω, if x q0 = a then g x else 0) / 16
      let var1 := fun a : Bool =>
        (∑ x : Ω, if x q0 = a then (g x) ^ 2 else 0) / 16 - (mean1 a) ^ 2
      let mean2 := fun a b : Bool =>
        (∑ x : Ω, if x q0 = a ∧ x (q1 a) = b then g x else 0) / 8
      let var2 := fun a b : Bool =>
        (∑ x : Ω,
          if x q0 = a ∧ x (q1 a) = b then (g x) ^ 2 else 0) / 8 -
          (mean2 a b) ^ 2
      let mean3 := fun a b c : Bool =>
        (∑ x : Ω,
          if x q0 = a ∧ x (q1 a) = b ∧ x (q2 a b) = c then g x else 0) / 4
      let var3 := fun a b c : Bool =>
        (∑ x : Ω,
          if x q0 = a ∧ x (q1 a) = b ∧ x (q2 a b) = c then (g x) ^ 2 else 0) / 4 -
          (mean3 a b c) ^ 2
      let mean4 := fun a b c d : Bool =>
        (∑ x : Ω,
          if x q0 = a ∧ x (q1 a) = b ∧ x (q2 a b) = c ∧
            x (q3 a b c) = d then g x else 0) / 2
      let var4 := fun a b c d : Bool =>
        (∑ x : Ω,
          if x q0 = a ∧ x (q1 a) = b ∧ x (q2 a b) = c ∧
            x (q3 a b c) = d then (g x) ^ 2 else 0) / 2 -
          (mean4 a b c d) ^ 2
      var0 + (∑ a : Bool, var1 a) / 2 +
        (∑ a : Bool, ∑ b : Bool, var2 a b) / 4 +
        (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, var3 a b c) / 8 +
        (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, var4 a b c d) / 16
  (∀ t : Tree, correlation t ≤ 15 / 16) ∧
    (∃ t : Tree, correlation t = 15 / 16) ∧
    (∃ q0 q1 q2 q3 q4, Fresh q0 q1 q2 q3 q4 ∧
      PolicyArea U q0 q1 q2 q3 q4 = 577 / 256) ∧
    (∀ q0 q1 q2 q3 q4, Fresh q0 q1 q2 q3 q4 →
      PolicyArea U q0 q1 q2 q3 q4 ≥ 577 / 256) ∧
    ((577 : ℚ) / 256) * ((15 : ℚ) / 16) ^ 2 = (129825 : ℚ) / 65536 ∧
    (129825 : ℚ) / 65536 < 2

end MathlibPlus.Open.Probability
