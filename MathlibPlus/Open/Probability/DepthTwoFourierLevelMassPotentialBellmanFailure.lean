import MathlibPlus.Basic

namespace MathlibPlus.Open.Probability

/--
The separate level-one/level-two Fourier `ℓ¹` budgets do not by themselves
produce the natural sharp Bellman potential
`quadraticMass + max linearMass quadraticMass`, even on an equal mixture of
two displayed depth-two Boolean selectors.  The prior variance is included.
-/
def depthTwoFourierLevelMassPotentialBellmanFailure : Prop :=
  let sign3 : Fin 8 → Fin 3 → ℚ := fun a i =>
    if Nat.testBit a.val i.val then 1 else -1
  let T : Fin 8 → ℚ := fun a =>
    if Nat.testBit a.val 2 then -sign3 a 1 else -sign3 a 0
  let U : Fin 8 → ℚ := fun a =>
    if Nat.testBit a.val 2 then -sign3 a 0 else sign3 a 1
  let g : Fin 8 → ℚ := fun a => (T a + U a) / 2
  let walsh3 : (Fin 8 → ℚ) → Fin 8 → ℚ := fun f mask =>
    (∑ a : Fin 8,
      (∏ i : Fin 3,
        if Nat.testBit mask.val i.val then sign3 a i else 1) * f a) / 8
  let linearMass3 : (Fin 8 → ℚ) → ℚ := fun f =>
    |walsh3 f 1| + |walsh3 f 2| + |walsh3 f 4|
  let quadraticMass3 : (Fin 8 → ℚ) → ℚ := fun f =>
    |walsh3 f 3| + |walsh3 f 5| + |walsh3 f 6|
  let potential3 : (Fin 8 → ℚ) → ℚ := fun f =>
    quadraticMass3 f + max (linearMass3 f) (quadraticMass3 f)
  let mean3 : (Fin 8 → ℚ) → ℚ := fun f => (∑ a : Fin 8, f a) / 8
  let variance3 : (Fin 8 → ℚ) → ℚ := fun f =>
    (∑ a : Fin 8, (f a - mean3 f) ^ 2) / 8
  let sign2 : Fin 4 → Fin 2 → ℚ := fun a i =>
    if Nat.testBit a.val i.val then 1 else -1
  let answer : Bool → ℚ := fun s => if s then 1 else -1
  let child : Fin 3 → Bool → Fin 4 → ℚ := fun i s a =>
    if i = 0 then -(answer s + sign2 a 0 * sign2 a 1) / 2
    else if i = 1 then -(sign2 a 0 + answer s * sign2 a 1) / 2
    else -(sign2 a 0 + sign2 a 1 * answer s) / 2
  let walsh2 : (Fin 4 → ℚ) → Fin 4 → ℚ := fun f mask =>
    (∑ a : Fin 4,
      (∏ i : Fin 2,
        if Nat.testBit mask.val i.val then sign2 a i else 1) * f a) / 4
  let linearMass2 : (Fin 4 → ℚ) → ℚ := fun f =>
    |walsh2 f 1| + |walsh2 f 2|
  let quadraticMass2 : (Fin 4 → ℚ) → ℚ := fun f => |walsh2 f 3|
  let potential2 : (Fin 4 → ℚ) → ℚ := fun f =>
    quadraticMass2 f + max (linearMass2 f) (quadraticMass2 f)
  (∀ a, (T a = -1 ∨ T a = 1) ∧ (U a = -1 ∨ U a = 1)) ∧
    (∀ a, g a = (T a + U a) / 2 ∧
      g a = -(sign3 a 0 + sign3 a 1 * sign3 a 2) / 2) ∧
    linearMass3 g = 1 / 2 ∧
    quadraticMass3 g = 1 / 2 ∧
    potential3 g = 1 ∧
    variance3 g = 1 / 2 ∧
    (∀ i s, potential2 (child i s) = 1) ∧
    ∀ i,
      potential3 g < variance3 g +
        (potential2 (child i false) + potential2 (child i true)) / 2

end MathlibPlus.Open.Probability
