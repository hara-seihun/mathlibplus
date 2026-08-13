import Mathlib

namespace MathlibPlus.Open.Probability

/--
On the uniform five-coordinate Boolean cube, the exact maximum optimal
posterior-variance areas for an equal mixture of five depth-at-most-two Boolean
functions, classified by semantic multiplicity with support at most four, are
`2`, `173 / 100`, `161 / 100`, `3 / 2`, `73 / 50`, and `67 / 50` for the six
patterns `5`, `4+1`, `3+2`, `3+1+1`, `2+2+1`, and `2+1+1+1`, respectively.

The proposition records the finite tree model, extensional semantic
multiplicity, fresh adaptive four-query policies, and the root-inclusive
expected conditional-variance area.  Each row has a universal upper policy
bound and an existential witness against every legal policy.
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
  let value : (Fin 5 → Tree) → Fin 5 → Ω → ℚ := fun trees i =>
    evalTree (trees i)
  let Pattern5 : (Fin 5 → Tree) → Prop := fun trees =>
    ∀ i j : Fin 5, value trees i = value trees j
  let Pattern41 : (Fin 5 → Tree) → Prop := fun trees =>
    ∃ e : Fin 5 ≃ Fin 5,
      value trees (e 0) = value trees (e 1) ∧
      value trees (e 1) = value trees (e 2) ∧
      value trees (e 2) = value trees (e 3) ∧
      value trees (e 4) ≠ value trees (e 0)
  let Pattern32 : (Fin 5 → Tree) → Prop := fun trees =>
    ∃ e : Fin 5 ≃ Fin 5,
      value trees (e 0) = value trees (e 1) ∧
      value trees (e 1) = value trees (e 2) ∧
      value trees (e 3) = value trees (e 4) ∧
      value trees (e 0) ≠ value trees (e 3)
  let Pattern311 : (Fin 5 → Tree) → Prop := fun trees =>
    ∃ e : Fin 5 ≃ Fin 5,
      value trees (e 0) = value trees (e 1) ∧
      value trees (e 1) = value trees (e 2) ∧
      value trees (e 0) ≠ value trees (e 3) ∧
      value trees (e 0) ≠ value trees (e 4) ∧
      value trees (e 3) ≠ value trees (e 4)
  let Pattern221 : (Fin 5 → Tree) → Prop := fun trees =>
    ∃ e : Fin 5 ≃ Fin 5,
      value trees (e 0) = value trees (e 1) ∧
      value trees (e 2) = value trees (e 3) ∧
      value trees (e 0) ≠ value trees (e 2) ∧
      value trees (e 0) ≠ value trees (e 4) ∧
      value trees (e 2) ≠ value trees (e 4)
  let Pattern2111 : (Fin 5 → Tree) → Prop := fun trees =>
    ∃ e : Fin 5 ≃ Fin 5,
      value trees (e 0) = value trees (e 1) ∧
      value trees (e 0) ≠ value trees (e 2) ∧
      value trees (e 0) ≠ value trees (e 3) ∧
      value trees (e 0) ≠ value trees (e 4) ∧
      value trees (e 2) ≠ value trees (e 3) ∧
      value trees (e 2) ≠ value trees (e 4) ∧
      value trees (e 3) ≠ value trees (e 4)
  let Fresh : Fin 5 → (Bool → Fin 5) → (Bool → Bool → Fin 5) →
      (Bool → Bool → Bool → Fin 5) → Prop :=
    fun q0 q1 q2 q3 =>
      (∀ a, q1 a ≠ q0) ∧
        (∀ a b, q2 a b ≠ q0 ∧ q2 a b ≠ q1 a) ∧
          ∀ a b c, q3 a b c ≠ q0 ∧ q3 a b c ≠ q1 a ∧
            q3 a b c ≠ q2 a b
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
      (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        var4 a b c d) / 16
  let target : (Fin 5 → Tree) → Ω → ℚ := fun trees x =>
    (∑ i : Fin 5, value trees i x) / 5
  (∀ trees : Fin 5 → Tree, Pattern5 trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target trees) q0 q1 q2 q3 ≤ 2) ∧
    (∀ trees : Fin 5 → Tree, Pattern41 trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target trees) q0 q1 q2 q3 ≤ 173 / 100) ∧
    (∀ trees : Fin 5 → Tree, Pattern32 trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target trees) q0 q1 q2 q3 ≤ 161 / 100) ∧
    (∀ trees : Fin 5 → Tree, Pattern311 trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target trees) q0 q1 q2 q3 ≤ 3 / 2) ∧
    (∀ trees : Fin 5 → Tree, Pattern221 trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target trees) q0 q1 q2 q3 ≤ 73 / 50) ∧
    (∀ trees : Fin 5 → Tree, Pattern2111 trees →
      ∃ q0 q1 q2 q3, Fresh q0 q1 q2 q3 ∧
        PolicyArea (target trees) q0 q1 q2 q3 ≤ 67 / 50) ∧
    (∃ trees : Fin 5 → Tree, Pattern5 trees ∧
      ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
        2 ≤ PolicyArea (target trees) q0 q1 q2 q3) ∧
    (∃ trees : Fin 5 → Tree, Pattern41 trees ∧
      ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
        173 / 100 ≤ PolicyArea (target trees) q0 q1 q2 q3) ∧
    (∃ trees : Fin 5 → Tree, Pattern32 trees ∧
      ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
        161 / 100 ≤ PolicyArea (target trees) q0 q1 q2 q3) ∧
    (∃ trees : Fin 5 → Tree, Pattern311 trees ∧
      ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
        3 / 2 ≤ PolicyArea (target trees) q0 q1 q2 q3) ∧
    (∃ trees : Fin 5 → Tree, Pattern221 trees ∧
      ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
        73 / 50 ≤ PolicyArea (target trees) q0 q1 q2 q3) ∧
    ∃ trees : Fin 5 → Tree, Pattern2111 trees ∧
      ∀ q0 q1 q2 q3, Fresh q0 q1 q2 q3 →
        67 / 50 ≤ PolicyArea (target trees) q0 q1 q2 q3

end MathlibPlus.Open.Probability
