import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

abbrev BooleanCube (n : ℕ) := Fin n → Bool

/-- The adjacent cube vertex obtained by changing coordinate `j`. -/
def flipCoordinate {n : ℕ} (x : BooleanCube n) (j : Fin n) : BooleanCube n :=
  Function.update x j (Bool.not (x j))

noncomputable def cubeCount {n : ℕ} (P : BooleanCube n → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

noncomputable def cubeExpectation {n : ℕ} (g : BooleanCube n → ℚ) : ℚ := by
  classical
  exact
    (∑ x ∈ (Finset.univ : Finset (BooleanCube n)), g x) /
      (Fintype.card (BooleanCube n) : ℚ)

noncomputable def conditionalExpectation {n : ℕ} (j : Fin n)
    (g : BooleanCube n → ℚ) : ℚ := by
  classical
  exact
    (∑ x ∈ (Finset.univ.filter (fun x => x j = false)), g x) /
      (cubeCount (fun x : BooleanCube n => x j = false) : ℚ)

noncomputable def conditionalProbability {n : ℕ} (j : Fin n)
    (P : BooleanCube n → Prop) : ℚ :=
  (cubeCount (fun x : BooleanCube n => x j = false ∧ P x) : ℚ) /
    (cubeCount (fun x : BooleanCube n => x j = false) : ℚ)

def boolValue (b : Bool) : ℚ :=
  if b = true then 1 else 0

noncomputable def directionDensity {n : ℕ} (f : BooleanCube n → Bool) : ℚ :=
  cubeExpectation (fun x => boolValue (f x))

noncomputable def directionDensityByIndex {n : ℕ}
    (f : Fin n → BooleanCube n → Bool) (i : Fin n) : ℚ :=
  directionDensity (f i)

noncomputable def upwardTransitionDensity {n : ℕ}
    (f : BooleanCube n → Bool) (j : Fin n) : ℚ :=
  conditionalProbability j
    (fun x => f x = false ∧ f (flipCoordinate x j) = true)

noncomputable def downwardTransitionDensity {n : ℕ}
    (f : BooleanCube n → Bool) (j : Fin n) : ℚ :=
  conditionalProbability j
    (fun x => f x = true ∧ f (flipCoordinate x j) = false)

noncomputable def literalTransitionDefect {n : ℕ}
    (f : BooleanCube n → Bool) (j : Fin n) : ℚ :=
  min (upwardTransitionDensity f j) (downwardTransitionDensity f j)

noncomputable def coordinateInfluence {n : ℕ}
    (f : BooleanCube n → Bool) (j : Fin n) : ℚ :=
  upwardTransitionDensity f j + downwardTransitionDensity f j

noncomputable def signedCoordinateChange {n : ℕ}
    (f : BooleanCube n → Bool) (j : Fin n) : ℚ :=
  conditionalExpectation j
    (fun x => boolValue (f (flipCoordinate x j)) - boolValue (f x))

def independentOfCoordinate {n : ℕ}
    (f : BooleanCube n → Bool) (i : Fin n) : Prop :=
  ∀ x y, (∀ k, k ≠ i → x k = y k) → f x = f y

def increasingAlong {n : ℕ}
    (f : BooleanCube n → Bool) (j : Fin n) : Prop :=
  ∀ x, x j = false →
    boolValue (f x) ≤ boolValue (f (flipCoordinate x j))

def decreasingAlong {n : ℕ}
    (f : BooleanCube n → Bool) (j : Fin n) : Prop :=
  ∀ x, x j = false →
    boolValue (f (flipCoordinate x j)) ≤ boolValue (f x)

/-- Claim 40425, on the Boolean cube with the conditional edge densities written
as finite uniform probabilities. -/
def literalTransitionDefectsClaim (n : ℕ)
    (f : Fin n → BooleanCube n → Bool) : Prop :=
  (∀ i, independentOfCoordinate (f i) i) ∧
    (∀ (i j : Fin n), i ≠ j →
      literalTransitionDefect (f i) j =
          (coordinateInfluence (f i) j -
            |signedCoordinateChange (f i) j|) / 2 ∧
        (literalTransitionDefect (f i) j = 0 ↔
          increasingAlong (f i) j ∨ decreasingAlong (f i) j))

end MathlibPlus.Open.ResearchFormalization
