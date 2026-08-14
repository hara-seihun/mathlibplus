import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Research

/-- The finite model of the five-coordinate Rademacher cube.  `0` and `1`
represent `-1` and `1`, respectively. -/
abbrev RademacherCube5 := Fin 5 → Fin 2

def rademacherValue (b : Fin 2) : ℝ :=
  if b = 0 then -1 else 1

def rademacherCharacter (A : Finset (Fin 5)) (x : RademacherCube5) : ℝ :=
  ∏ i ∈ A, rademacherValue (x i)

def cubeAverage (f : RademacherCube5 → ℝ) : ℝ :=
  (1 / (Fintype.card RademacherCube5 : ℝ)) * ∑ x, f x

def walshCoefficient (u : RademacherCube5 → ℝ)
    (A : Finset (Fin 5)) : ℝ :=
  cubeAverage (fun x => u x * rademacherCharacter A x)

def centered (u : RademacherCube5 → ℝ) : Prop :=
  cubeAverage u = 0

def shapleyIndex (u : RademacherCube5 → ℝ) (i : Fin 5) : ℝ :=
  ∑ A : Finset (Fin 5),
    if i ∈ A then
      walshCoefficient u A ^ 2 / (A.card : ℝ)
    else 0

inductive DecisionTree (n : Nat) where
  | leaf : DecisionTree n
  | node (i : Fin n) (negative positive : DecisionTree n) : DecisionTree n

def queriedCoordinates : DecisionTree n → (Fin n → Fin 2) → Finset (Fin n)
  | .leaf, _ => ∅
  | .node i negative positive, x =>
      insert i
        (if x i = 0 then queriedCoordinates negative x
         else queriedCoordinates positive x)

def allCoordinates : DecisionTree n → Finset (Fin n)
  | .leaf => ∅
  | .node i negative positive =>
      insert i (allCoordinates negative ∪ allCoordinates positive)

def nonrepeating : DecisionTree n → Prop
  | .leaf => True
  | .node i negative positive =>
      nonrepeating negative ∧ nonrepeating positive ∧
        i ∉ allCoordinates negative ∧ i ∉ allCoordinates positive

def revealment (T : DecisionTree 5) (i : Fin 5) : ℝ :=
  cubeAverage (fun x => if i ∈ queriedCoordinates T x then 1 else 0)

def weightedRevealmentArea (T : DecisionTree 5)
    (u : RademacherCube5 → ℝ) : ℝ :=
  ∑ i : Fin 5, revealment T i * shapleyIndex u i

/-- Claim 50224: the query-revealment expression is the Walsh expansion of
`D_T(u)` for a centered function and a deterministic nonrepeating tree. -/
def claim50224 : Prop :=
  ∀ (u : RademacherCube5 → ℝ) (T : DecisionTree 5),
    centered u → nonrepeating T →
      weightedRevealmentArea T u =
        ∑ A : Finset (Fin 5),
          if A.Nonempty then
            walshCoefficient u A ^ 2 *
              ((∑ i ∈ A, revealment T i) / (A.card : ℝ))
          else 0

def witnessU (x : RademacherCube5) : ℝ :=
  -(7 : ℝ) / 3 * rademacherCharacter ({2} : Finset (Fin 5)) x
    + (14 : ℝ) / 15 *
        rademacherCharacter ({0, 2} : Finset (Fin 5)) x
    - (14 : ℝ) / 9 *
        rademacherCharacter ({1, 2} : Finset (Fin 5)) x
    + rademacherCharacter ({0, 1, 2} : Finset (Fin 5)) x

/-- Claim 50235: the displayed four Walsh coefficients are the only nonzero
coefficients of the displayed centered witness. -/
def claim50235 : Prop :=
  walshCoefficient witnessU ({2} : Finset (Fin 5)) = -(7 : ℝ) / 3 ∧
    walshCoefficient witnessU ({0, 2} : Finset (Fin 5)) = (14 : ℝ) / 15 ∧
    walshCoefficient witnessU ({1, 2} : Finset (Fin 5)) = -(14 : ℝ) / 9 ∧
    walshCoefficient witnessU ({0, 1, 2} : Finset (Fin 5)) = 1 ∧
    walshCoefficient witnessU (∅ : Finset (Fin 5)) = 0 ∧
    centered witnessU ∧
    ∀ A : Finset (Fin 5),
      A ≠ ({2} : Finset (Fin 5)) →
      A ≠ ({0, 2} : Finset (Fin 5)) →
      A ≠ ({1, 2} : Finset (Fin 5)) →
      A ≠ ({0, 1, 2} : Finset (Fin 5)) →
      walshCoefficient witnessU A = 0

end MathlibPlus.Open.Research
