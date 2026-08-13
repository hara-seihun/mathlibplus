import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Field

namespace MathlibPlus.Open.Probability

/--
On the uniform five-coordinate Boolean cube, the exact maximum optimal
root-inclusive posterior-variance areas of denominator-eight depth-at-most-two
laws with four pairwise-distinct semantic tables are `23 / 16` in the
multiplicity stratum `3+3+1+1` and `179 / 128` in the stratum `3+2+2+1`.
-/
def denominatorEightAllLightSupportFourDepthTwoFiveCubeAreaMaxima : Prop :=
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
  let Same : Tree → Tree → Prop := fun t u => evalTree t = evalTree u
  let Distinct : (Fin 4 → Tree) → Prop := fun trees =>
    ¬ Same (trees 0) (trees 1) ∧ ¬ Same (trees 0) (trees 2) ∧
      ¬ Same (trees 0) (trees 3) ∧ ¬ Same (trees 1) (trees 2) ∧
      ¬ Same (trees 1) (trees 3) ∧ ¬ Same (trees 2) (trees 3)
  let Fresh : Fin 5 → (Bool → Fin 5) → (Bool → Bool → Fin 5) →
      (Bool → Bool → Bool → Fin 5) → Prop := fun q0 q1 q2 q3 =>
    (∀ a, q1 a ≠ q0) ∧
      (∀ a b, q2 a b ≠ q0 ∧ q2 a b ≠ q1 a) ∧
      ∀ a b c, q3 a b c ≠ q0 ∧ q3 a b c ≠ q1 a ∧ q3 a b c ≠ q2 a b
  let PolicyArea : (Ω → ℚ) → Fin 5 → (Bool → Fin 5) →
      (Bool → Bool → Fin 5) → (Bool → Bool → Bool → Fin 5) → ℚ :=
    fun g q0 q1 q2 q3 =>
      let mean0 := (∑ x : Ω, g x) / 32
      let var0 := (∑ x : Ω, (g x) ^ 2) / 32 - mean0 ^ 2
      let mean1 := fun a : Bool =>
        (∑ x : Ω, if x q0 = a then g x else 0) / 16
      let var1 := fun a : Bool =>
        (∑ x : Ω, if x q0 = a then (g x) ^ 2 else 0) / 16 - (mean1 a) ^ 2
      let mean2 := fun a b : Bool =>
        (∑ x : Ω, if x q0 = a ∧ x (q1 a) = b then g x else 0) / 8
      let var2 := fun a b : Bool =>
        (∑ x : Ω, if x q0 = a ∧ x (q1 a) = b then (g x) ^ 2 else 0) / 8 -
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
          if x q0 = a ∧ x (q1 a) = b ∧ x (q2 a b) = c ∧ x (q3 a b c) = d
          then g x else 0) / 2
      let var4 := fun a b c d : Bool =>
        (∑ x : Ω,
          if x q0 = a ∧ x (q1 a) = b ∧ x (q2 a b) = c ∧ x (q3 a b c) = d
          then (g x) ^ 2 else 0) / 2 - (mean4 a b c d) ^ 2
      var0 + (∑ a : Bool, var1 a) / 2 +
        (∑ a : Bool, ∑ b : Bool, var2 a b) / 4 +
        (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, var3 a b c) / 8 +
        (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, var4 a b c d) / 16
  let target3311 : (Fin 4 → Tree) → Ω → ℚ := fun trees x =>
    (3 * evalTree (trees 0) x + 3 * evalTree (trees 1) x +
      evalTree (trees 2) x + evalTree (trees 3) x) / 8
  let target3221 : (Fin 4 → Tree) → Ω → ℚ := fun trees x =>
    (3 * evalTree (trees 0) x + 2 * evalTree (trees 1) x +
      2 * evalTree (trees 2) x + evalTree (trees 3) x) / 8
  (∀ trees : Fin 4 → Tree, Distinct trees →
    ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
      PolicyArea (target3311 trees) q0 q1 q2 q3 ≤ 23 / 16) ∧
    (∃ trees : Fin 4 → Tree, Distinct trees ∧
      ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
        23 / 16 ≤ PolicyArea (target3311 trees) q0 q1 q2 q3) ∧
    (∀ trees : Fin 4 → Tree, Distinct trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target3221 trees) q0 q1 q2 q3 ≤ 179 / 128) ∧
    ∃ trees : Fin 4 → Tree, Distinct trees ∧
      ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
        179 / 128 ≤ PolicyArea (target3221 trees) q0 q1 q2 q3

end MathlibPlus.Open.Probability
