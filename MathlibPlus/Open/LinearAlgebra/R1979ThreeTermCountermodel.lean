import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.R1979

/-- The explicit integer transport matrices of the countermodel. -/
def partialN : Matrix (Fin 3) (Fin 2) ℤ :=
  !![1, 0; -1, 1; 0, -1]

def sigma : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 1, 1, 0; 0, 1, 2]

def partialM : Matrix (Fin 3) (Fin 2) ℤ :=
  !![1, 0; 0, 1; -1, -1]

def topBoundaryT : Fin 3 → ℤ := ![1, 0, 0]
def topBoundaryV : Fin 3 → ℤ := ![0, 1, 0]
def topBoundaryU : Fin 3 → ℤ := ![0, 0, 1]

def lowerInvariantA : Fin 2 → ℚ := ![1, 1]
def lowerInvariantB : Fin 2 → ℚ := ![1, -1]
def lowerInvariantC : Fin 2 → ℚ := ![1, 0]

def pairwiseIndependentLowerInvariants : Prop :=
  LinearIndependent ℚ (fun i : Fin 2 =>
    match i with
    | 0 => lowerInvariantA
    | 1 => lowerInvariantB) ∧
  LinearIndependent ℚ (fun i : Fin 2 =>
    match i with
    | 0 => lowerInvariantA
    | 1 => lowerInvariantC) ∧
  LinearIndependent ℚ (fun i : Fin 2 =>
    match i with
    | 0 => lowerInvariantB
    | 1 => lowerInvariantC)

/-- The explicit commuting transport countermodel: telescoping top boundaries
coexist with a support-minimal non-binomial lower relation. -/
def claim_36716 : Prop :=
  sigma * partialN = partialM ∧
    (topBoundaryT - topBoundaryV) + (topBoundaryV - topBoundaryU) =
      topBoundaryT - topBoundaryU ∧
    (lowerInvariantA + lowerInvariantB - 2 • lowerInvariantC = 0) ∧
    pairwiseIndependentLowerInvariants ∧
    ¬ ∃ i j : Fin 3, i ≠ j ∧
      (match i with
       | 0 => lowerInvariantA
       | 1 => lowerInvariantB
       | 2 => lowerInvariantC) =
      (match j with
       | 0 => lowerInvariantA
       | 1 => lowerInvariantB
       | 2 => lowerInvariantC)

end MathlibPlus.Open.LinearAlgebra.R1979
