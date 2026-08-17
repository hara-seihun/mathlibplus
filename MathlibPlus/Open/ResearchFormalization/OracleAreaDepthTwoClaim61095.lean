import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoClaim61095

noncomputable section
open Classical

abbrev Coordinate := Fin 6
abbrev Outcome := Coordinate → Bool

def signValue : Bool → ℝ
  | false => -1
  | true => 1

def cubeAverage (f : Outcome → ℝ) : ℝ :=
  (Fintype.card Outcome : ℝ)⁻¹ * ∑ x : Outcome, f x

def signCoordinate (i : Coordinate) (x : Outcome) : ℝ :=
  signValue (x i)

def selectorOne (x : Outcome) : ℝ :=
  (-signCoordinate 0 x + signCoordinate 3 x +
      signCoordinate 0 x * signCoordinate 4 x +
      signCoordinate 3 x * signCoordinate 4 x) / 2

def selectorTwo (x : Outcome) : ℝ :=
  (-signCoordinate 0 x + signCoordinate 3 x -
      signCoordinate 0 x * signCoordinate 4 x -
      signCoordinate 3 x * signCoordinate 4 x) / 2

def selectorThree (x : Outcome) : ℝ :=
  (signCoordinate 1 x - signCoordinate 2 x -
      signCoordinate 1 x * signCoordinate 5 x -
      signCoordinate 2 x * signCoordinate 5 x) / 2

/-- A Boolean deterministic query tree used to record the depth-two legality of
The three displayed selectors. -/
inductive SelectorTree where
  | leaf : Bool → SelectorTree
  | query : Coordinate → SelectorTree → SelectorTree → SelectorTree

def SelectorTree.eval : SelectorTree → Outcome → Bool
  | .leaf value, _ => value
  | .query q negative positive, x =>
      if x q then positive.eval x else negative.eval x

def SelectorTree.depth : SelectorTree → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max negative.depth positive.depth

def noRepeatedQueries (used : Finset Coordinate) : SelectorTree → Prop
  | .leaf _ => True
  | .query q negative positive =>
      q ∉ used ∧
        noRepeatedQueries (insert q used) negative ∧
          noRepeatedQueries (insert q used) positive

def legalSelectorTree (tree : SelectorTree) : Prop :=
  tree.depth ≤ 2 ∧ noRepeatedQueries ∅ tree

def selectorTreeOne : SelectorTree :=
  .query 4
    (.query 0 (.leaf true) (.leaf false))
    (.query 3 (.leaf false) (.leaf true))

def selectorTreeTwo : SelectorTree :=
  .query 4
    (.query 3 (.leaf false) (.leaf true))
    (.query 0 (.leaf true) (.leaf false))

def selectorTreeThree : SelectorTree :=
  .query 5
    (.query 1 (.leaf false) (.leaf true))
    (.query 2 (.leaf true) (.leaf false))

def mixtureMean (x : Outcome) : ℝ :=
  (9 / 91 : ℝ) * selectorOne x +
    (45 / 91 : ℝ) * selectorTwo x +
      (37 / 91 : ℝ) * selectorThree x

def walshCoefficient (m : Outcome → ℝ) (r : Coordinate) : ℝ :=
  cubeAverage (fun x => m x * signCoordinate r x)

def pairWalshCoefficient (m : Outcome → ℝ)
    (r s : Coordinate) : ℝ :=
  if r = s then 0 else
    cubeAverage (fun x =>
      m x * signCoordinate r x * signCoordinate s x)

def linearCoefficient (r : Coordinate) : ℝ :=
  walshCoefficient mixtureMean r

def quadraticCoefficient (r s : Coordinate) : ℝ :=
  pairWalshCoefficient mixtureMean r s

def quadraticLoad (r : Coordinate) : ℝ :=
  ∑ s : Coordinate, if s = r then 0 else |quadraticCoefficient r s|

def maximumLoad (r : Coordinate) : ℝ :=
  max (|linearCoefficient r| + quadraticLoad r / 2)
    (|linearCoefficient r| / 2 + quadraticLoad r)

def restrictedMean (i : Coordinate) (x : Bool) (y : Outcome) : ℝ :=
  mixtureMean (Function.update y i x)

def restrictedLinearCoefficient (i : Coordinate) (x : Bool)
    (j : Coordinate) : ℝ :=
  cubeAverage (fun y =>
    restrictedMean i x y * signCoordinate j y)

def restrictedQuadraticCoefficient (i : Coordinate) (x : Bool)
    (j k : Coordinate) : ℝ :=
  pairWalshCoefficient (restrictedMean i x) j k

def restrictedQuadraticLoad (i : Coordinate) (x : Bool)
    (j : Coordinate) : ℝ :=
  ∑ k : Coordinate,
    if k = i ∨ k = j then 0
    else |restrictedQuadraticCoefficient i x j k|

def restrictedMaximumLoad (i : Coordinate) (x : Bool)
    (j : Coordinate) : ℝ :=
  max (|restrictedLinearCoefficient i x j| +
      restrictedQuadraticLoad i x j / 2)
    (|restrictedLinearCoefficient i x j| / 2 +
      restrictedQuadraticLoad i x j)

def branchMaximum (i : Coordinate) (x : Bool) : ℝ :=
  sSup {v : ℝ |
    ∃ j : Coordinate, j ≠ i ∧ v = restrictedMaximumLoad i x j}

def varianceEnergy : ℝ :=
  ∑ r : Coordinate, (linearCoefficient r) ^ 2 +
    ∑ r : Coordinate, ∑ s : Coordinate,
      if r < s then (quadraticCoefficient r s) ^ 2 else 0

/-- Claim 61095: the exact legal depth-two selectors give the displayed
quadratic Walsh data and disprove the proposed two-level maximum-load packet
inequality at coordinate `5`. -/
def claim61095 : Prop :=
  (legalSelectorTree selectorTreeOne ∧
    legalSelectorTree selectorTreeTwo ∧
      legalSelectorTree selectorTreeThree) ∧
  (∀ x : Outcome,
    signValue (selectorTreeOne.eval x) = selectorOne x ∧
      signValue (selectorTreeTwo.eval x) = selectorTwo x ∧
        signValue (selectorTreeThree.eval x) = selectorThree x) ∧
  (∀ r : Coordinate,
    maximumLoad r ≤ maximumLoad 5 ∧
      (maximumLoad r = maximumLoad 5 → r = 5)) ∧
  maximumLoad 0 = 36 / 91 ∧
    maximumLoad 1 = 111 / 364 ∧
      maximumLoad 2 = 111 / 364 ∧
        maximumLoad 3 = 36 / 91 ∧
          maximumLoad 4 = 36 / 91 ∧
            maximumLoad 5 = 37 / 91 ∧
  varianceEnergy = 3475 / 8281 ∧
  branchMaximum 5 false = 37 / 91 ∧
    branchMaximum 5 true = 37 / 91 ∧
  2 * varianceEnergy - (linearCoefficient 5) ^ 2 = 6950 / 8281 ∧
    maximumLoad 5 + (1 / 2 : ℝ) *
        ∑ x : Bool, branchMaximum 5 x = 74 / 91 ∧
      2 * varianceEnergy - (linearCoefficient 5) ^ 2 >
        maximumLoad 5 + (1 / 2 : ℝ) *
          ∑ x : Bool, branchMaximum 5 x ∧
        (2 * varianceEnergy - (linearCoefficient 5) ^ 2) -
            (maximumLoad 5 + (1 / 2 : ℝ) *
              ∑ x : Bool, branchMaximum 5 x) = 216 / 8281

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoClaim61095
