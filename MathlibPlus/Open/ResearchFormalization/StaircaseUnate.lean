import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev BooleanCube (n : Nat) := Fin n → Bool

/-- The order on `Bool`, written without relying on a project-specific order instance. -/
def boolLe (a b : Bool) : Prop := a = false ∨ b = true

/-- A Boolean direction function with the staircase monotonicity and its own-coordinate
independence stated in Claim 40349. -/
def staircaseUnate {n : Nat} (i : Fin n)
    (f : BooleanCube n → Bool) : Prop :=
  (∀ x, f x = f (Function.update x i false)) ∧
  (∀ (j : Fin n), j < i → ∀ x,
    boolLe (f (Function.update x j true)) (f (Function.update x j false))) ∧
  (∀ (j : Fin n), i < j → ∀ x,
    boolLe (f (Function.update x j false)) (f (Function.update x j true)))

/-- A square is complete when all four of its coordinate edges are present. -/
def squareComplete {n : Nat} (f : Fin n → BooleanCube n → Bool)
    (i j : Fin n) (x : BooleanCube n) : Prop :=
  f i x = true ∧
    f i (Function.update x j true) = true ∧
    f j x = true ∧
    f j (Function.update x i true) = true

/-- Claim 40349, with `Q_n` represented by `Fin n → Bool` and `x + e_i` by
updating the zero `i`-coordinate to one. -/
def claim_40349 : Prop :=
  ∀ (n : Nat) (f : Fin n → BooleanCube n → Bool),
    (∀ i, staircaseUnate i (f i)) →
      ∀ (i j : Fin n), i < j →
        ∀ x, x i = false → x j = false →
          (squareComplete f i j x ↔
            f i x && f j (Function.update x i true) = true)

abbrev Q5 := BooleanCube 5

def q5f0 (x : Q5) : Bool := x 1 && (x 2 || x 3)
def q5f1 (x : Q5) : Bool := x 2 || x 3
def q5f2 (x : Q5) : Bool := (!x 1) && x 3
def q5f3 (x : Q5) : Bool := (!x 1) || (!x 2)
def q5f4 (x : Q5) : Bool := (!x 3) && ((!x 1) || (!x 2))

def q5Family (i : Fin 5) : Q5 → Bool :=
  match i.1 with
  | 0 => q5f0
  | 1 => q5f1
  | 2 => q5f2
  | 3 => q5f3
  | _ => q5f4

/-- Claim 40350. `staircaseUnate` also records independence of each function's own
coordinate, as required by the claim. -/
def claim_40350 : Prop :=
  staircaseUnate 0 q5f0 ∧
    staircaseUnate 1 q5f1 ∧
    staircaseUnate 2 q5f2 ∧
    staircaseUnate 3 q5f3 ∧
    staircaseUnate 4 q5f4

end MathlibPlus.Open.ResearchFormalization
