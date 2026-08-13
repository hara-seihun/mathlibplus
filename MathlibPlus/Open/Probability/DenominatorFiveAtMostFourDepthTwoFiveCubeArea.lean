import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Field

namespace MathlibPlus.Open.Probability

/--
On the uniform five-coordinate Boolean cube, the six semantic multiplicity
strata of five equal draws from at most four depth-at-most-two Boolean
functions have exact optimal posterior-variance area maxima `2`, `173 / 100`,
`161 / 100`, `3 / 2`, `73 / 50`, and `67 / 50` for patterns `5`, `4+1`,
`3+2`, `3+1+1`, `2+2+1`, and `2+1+1+1`, respectively.

A policy is encoded by its first four fresh adaptive queries. Querying the
unique fifth coordinate afterward makes every target measurable, and any
earlier measurability contributes zero conditional variance. Thus
`PolicyArea` is exactly the cumulative area, including the prior variance.
-/
def denominatorFiveAtMostFourDepthTwoFiveCubeAreaMaxima : Prop :=
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
  let Pattern5 : (Fin 5 → Tree) → Prop := fun trees =>
    Same (trees 0) (trees 1) ∧ Same (trees 1) (trees 2) ∧
      Same (trees 2) (trees 3) ∧ Same (trees 3) (trees 4)
  let Pattern41 : (Fin 5 → Tree) → Prop := fun trees =>
    Same (trees 0) (trees 1) ∧ Same (trees 1) (trees 2) ∧
      Same (trees 2) (trees 3) ∧ ¬ Same (trees 3) (trees 4)
  let Pattern32 : (Fin 5 → Tree) → Prop := fun trees =>
    Same (trees 0) (trees 1) ∧ Same (trees 1) (trees 2) ∧
      Same (trees 3) (trees 4) ∧ ¬ Same (trees 0) (trees 3)
  let Pattern311 : (Fin 5 → Tree) → Prop := fun trees =>
    Same (trees 0) (trees 1) ∧ Same (trees 1) (trees 2) ∧
      ¬ Same (trees 0) (trees 3) ∧ ¬ Same (trees 0) (trees 4) ∧
      ¬ Same (trees 3) (trees 4)
  let Pattern221 : (Fin 5 → Tree) → Prop := fun trees =>
    Same (trees 0) (trees 1) ∧ Same (trees 2) (trees 3) ∧
      ¬ Same (trees 0) (trees 2) ∧ ¬ Same (trees 0) (trees 4) ∧
      ¬ Same (trees 2) (trees 4)
  let Pattern2111 : (Fin 5 → Tree) → Prop := fun trees =>
    Same (trees 0) (trees 1) ∧ ¬ Same (trees 0) (trees 2) ∧
      ¬ Same (trees 0) (trees 3) ∧ ¬ Same (trees 0) (trees 4) ∧
      ¬ Same (trees 2) (trees 3) ∧ ¬ Same (trees 2) (trees 4) ∧
      ¬ Same (trees 3) (trees 4)
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
  let target : (Fin 5 → Tree) → Ω → ℚ := fun trees x =>
    (∑ i : Fin 5, evalTree (trees i) x) / 5
  let Attains : ((Fin 5 → Tree) → Prop) → ℚ → Prop := fun pattern bound =>
    (∀ trees : Fin 5 → Tree, pattern trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target trees) q0 q1 q2 q3 ≤ bound) ∧
      ∃ trees : Fin 5 → Tree, pattern trees ∧
        ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
          bound ≤ PolicyArea (target trees) q0 q1 q2 q3
  Attains Pattern5 2 ∧ Attains Pattern41 (173 / 100) ∧
    Attains Pattern32 (161 / 100) ∧ Attains Pattern311 (3 / 2) ∧
    Attains Pattern221 (73 / 50) ∧ Attains Pattern2111 (67 / 50)

end MathlibPlus.Open.Probability
