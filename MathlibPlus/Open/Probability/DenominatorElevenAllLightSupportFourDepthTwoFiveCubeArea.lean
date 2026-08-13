import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Field

namespace MathlibPlus.Open.Probability

noncomputable section
open scoped Classical

/--
On the uniform five-coordinate Boolean cube, the exact maximum optimal
root-inclusive posterior-variance areas of denominator-eleven all-light
depth-at-most-two laws with four pairwise-distinct semantic tables are
`1345/968`, `687/484`, `1385/968`, `1335/968`, and `667/484` in the five
multiplicity strata.
-/
def denominatorElevenAllLightSupportFourDepthTwoFiveCubeAreaMaxima : Prop :=
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
  let Fresh : Fin 5 → (Bool → Fin 5) →
      (Bool → Bool → Fin 5) → (Bool → Bool → Bool → Fin 5) → Prop :=
    fun q0 q1 q2 q3 =>
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
        (∑ x : Ω, if x q0 = a then (g x) ^ 2 else 0) / 16 -
          (mean1 a) ^ 2
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
      var0 + (∑ a : Bool, var1 a) / 2 +
        (∑ a : Bool, ∑ b : Bool, var2 a b) / 4 +
        (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, var3 a b c) / 8
  let Target := (Fin 4 → Tree) → (Fin 4 → ℚ) → Ω → ℚ
  let target : Target := fun trees weights x =>
    (∑ i : Fin 4, weights i * evalTree (trees i) x) / 11
  let Attains : (Fin 4 → ℚ) → ℚ → Prop := fun weights bound =>
    (∀ trees : Fin 4 → Tree, Distinct trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target trees weights) q0 q1 q2 q3 ≤ bound) ∧
      ∃ trees : Fin 4 → Tree, Distinct trees ∧
        ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
          bound ≤ PolicyArea (target trees weights) q0 q1 q2 q3
  Attains ![5, 3, 2, 1] (1345 / 968) ∧
    Attains ![4, 4, 2, 1] (687 / 484) ∧
    Attains ![4, 3, 3, 1] (1385 / 968) ∧
    Attains ![4, 3, 2, 2] (1335 / 968) ∧
    Attains ![3, 3, 3, 2] (667 / 484)

end
end MathlibPlus.Open.Probability
