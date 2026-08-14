import Mathlib

namespace MathlibPlus.Open.Carry.Transition

inductive Digit where
  | zero
  | one
  deriving DecidableEq, Repr

instance : Fintype Digit where
  elems := {.zero, .one}
  complete := by
    intro e
    cases e <;> simp

def digitValue : Digit → ℤ
  | .zero => 0
  | .one => 1

def carryNext (n : Nat) (S : ℤ) (e : Digit) : ℤ :=
  2 * S + ((n + 1 : Nat) : ℤ) * (1 - 2 * digitValue e)

def feasible (n : Nat) (S : ℤ) : Prop :=
  |S| ≤ ((n + 2 : Nat) : ℤ)

def atBoundary (n : Nat) (S : ℤ) : Prop :=
  |S| = ((n + 2 : Nat) : ℤ)

/-- The unique continuation equations away from the central state. -/
def UniqueNonboundaryChild : Prop :=
  ∀ (n : Nat) (S : ℤ), feasible n S →
    ((1 < S →
      ∃! e : Digit,
        feasible (n + 1) (carryNext n S e) ∧
          carryNext n S e = 2 * S - ((n + 1 : Nat) : ℤ)) ∧
     (S < -1 →
      ∃! e : Digit,
        feasible (n + 1) (carryNext n S e) ∧
          carryNext n S e = 2 * S + ((n + 1 : Nat) : ℤ)))

/-- Central children and the two exact boundary/continuation alternatives. -/
def CentralAndBoundaryCarryFacts : Prop :=
  (∀ k : Nat, Even k →
    carryNext k 0 .zero = ((k + 1 : Nat) : ℤ) ∧
      carryNext k 0 .one = -((k + 1 : Nat) : ℤ) ∧
      carryNext k 0 .one = -carryNext k 0 .zero) ∧
  (∀ n : Nat,
    carryNext n 1 .zero = ((n + 3 : Nat) : ℤ) ∧
      atBoundary (n + 1) (carryNext n 1 .zero) ∧
      carryNext n 1 .one = 2 * (1 : ℤ) - ((n + 1 : Nat) : ℤ) ∧
      feasible (n + 1) (carryNext n 1 .one) ∧
      ¬ atBoundary (n + 1) (carryNext n 1 .one) ∧
      carryNext n (-1 : ℤ) .one = -((n + 3 : Nat) : ℤ) ∧
      atBoundary (n + 1) (carryNext n (-1 : ℤ) .one) ∧
      carryNext n (-1 : ℤ) .zero =
        2 * (-1 : ℤ) + ((n + 1 : Nat) : ℤ) ∧
      feasible (n + 1) (carryNext n (-1 : ℤ) .zero) ∧
      ¬ atBoundary (n + 1) (carryNext n (-1 : ℤ) .zero))

/-- The complete admitted local carry transition assertion. -/
def CenteredCarryTransitionClaim : Prop :=
  UniqueNonboundaryChild ∧ CentralAndBoundaryCarryFacts

end MathlibPlus.Open.Carry.Transition
