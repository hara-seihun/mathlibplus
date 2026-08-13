import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Field

namespace MathlibPlus.Open.Probability

/--
On the uniform four-coordinate Boolean cube, for four pairwise distinct semantic
Boolean functions computed by depth-at-most-two decision trees, the exact
maximal optimal posterior-variance areas on the strict all-light positive
integer weight grids of total weight `4` through `20` are recorded below.
A policy is encoded by its first three fresh adaptive queries; the forced
fourth query leaves zero variance. The prior variance is included.
-/
def allLightFourCubeWeightGridThroughTwenty : Prop :=
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
    ∀ i j, i ≠ j → evalTree (trees i) ≠ evalTree (trees j)
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
  let target : ℕ → (Fin 4 → ℕ) → (Fin 4 → Tree) → Ω → ℚ :=
    fun W weights trees x =>
      (∑ i : Fin 4, (weights i : ℚ) * evalTree (trees i) x) / W
  let AllLight : ℕ → (Fin 4 → ℕ) → Prop := fun W weights =>
    (∀ i, 0 < weights i) ∧
      (∀ i, 2 * weights i < W)
  let Attains : ℕ → ℚ → Prop := fun W bound =>
    (∀ weights : Fin 4 → ℕ, AllLight W weights →
      (∑ i : Fin 4, weights i) = W →
      ∀ trees : Fin 4 → Tree, Distinct trees →
        ∃ q0 q1 q2, Fresh q0 q1 q2 ∧
          PolicyArea (target W weights trees) q0 q1 q2 ≤ bound) ∧
      ∃ weights : Fin 4 → ℕ, AllLight W weights ∧
        (∑ i : Fin 4, weights i) = W ∧
        ∃ trees : Fin 4 → Tree, Distinct trees ∧
          ∀ q0 q1 q2, Fresh q0 q1 q2 →
            bound ≤ PolicyArea (target W weights trees) q0 q1 q2
  Attains 4 (41 / 32) ∧
    Attains 5 (133 / 100) ∧
    Attains 6 (4 / 3) ∧
    Attains 7 (67 / 49) ∧
    Attains 8 (353 / 256) ∧
    Attains 9 (229 / 162) ∧
    Attains 10 (141 / 100) ∧
    Attains 11 (697 / 484) ∧
    Attains 12 (275 / 192) ∧
    Attains 13 (246 / 169) ∧
    Attains 14 (569 / 392) ∧
    Attains 15 (1321 / 900) ∧
    Attains 16 (47 / 32) ∧
    Attains 17 (427 / 289) ∧
    Attains 18 (961 / 648) ∧
    Attains 19 (4301 / 2888) ∧
    Attains 20 (299 / 200)

end MathlibPlus.Open.Probability
