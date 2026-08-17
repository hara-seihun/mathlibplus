import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.OracleArea.ConstructivePolicySquaredDepthTailClaim61165

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev Cube3 := Fin 3 → Bool
abbrev Cell3 := Fin 3 → Option Bool

def rowIndex (x : Cube3) : ℕ :=
  (if x 0 then 1 else 0) +
    2 * (if x 1 then 1 else 0) +
      4 * (if x 2 then 1 else 0)

def maskSign (m : ℕ) (x : Cube3) : Bool :=
  Nat.testBit m (rowIndex x)

def atomH : Cube3 → Bool := maskSign 139
def atomEll : Cube3 → Bool := maskSign 15

def signValue (b : Bool) : ℝ := if b then 1 else -1

def realH (x : Cube3) : ℝ := signValue (atomH x)
def realEll (x : Cube3) : ℝ := signValue (atomEll x)
def targetG (x : Cube3) : ℝ := (3 / 4 : ℝ) * realH x + (1 / 4 : ℝ) * realEll x

def cellConsistent (C : Cell3) (x : Cube3) : Prop :=
  ∀ i b, C i = some b → x i = b

def usedCoordinates (C : Cell3) : Finset (Fin 3) :=
  (Finset.univ : Finset (Fin 3)).filter (fun i => (C i).isSome)

def extendCell (C : Cell3) (i : Fin 3) (b : Bool) : Cell3 :=
  Function.update C i (some b)

def cellCard (C : Cell3) : ℕ :=
  Set.ncard {x : Cube3 | cellConsistent C x}

def cellAverage (C : Cell3) (g : Cube3 → ℝ) : ℝ :=
  (∑ x : Cube3, if cellConsistent C x then g x else 0) /
    (cellCard C : ℝ)

def cellMean (C : Cell3) (g : Cube3 → ℝ) : ℝ :=
  cellAverage C g

def cellVariance (C : Cell3) (g : Cube3 → ℝ) : ℝ :=
  cellAverage C (fun x => g x ^ 2) - (cellMean C g) ^ 2

inductive DecisionTree
  | leaf (value : Bool)
  | query (i : Fin 3) (ifFalse ifTrue : DecisionTree)

def treeDepth : DecisionTree → ℕ
  | .leaf _ => 0
  | .query _ ifFalse ifTrue => 1 + max (treeDepth ifFalse) (treeDepth ifTrue)

def treeValue : DecisionTree → Cube3 → Bool
  | .leaf value, _ => value
  | .query i ifFalse ifTrue, x =>
      if x i then treeValue ifTrue x else treeValue ifFalse x

def legalTreeAt : Finset (Fin 3) → DecisionTree → Prop
  | _, .leaf _ => True
  | used, .query i ifFalse ifTrue =>
      i ∉ used ∧
        legalTreeAt (insert i used) ifFalse ∧
          legalTreeAt (insert i used) ifTrue

def computesOnCell
    (target : Cube3 → Bool) (C : Cell3) (tree : DecisionTree) : Prop :=
  ∀ x, cellConsistent C x → treeValue tree x = target x

def minimumResidualDepth
    (target : Cube3 → Bool) (C : Cell3) : ℕ :=
  sInf {d : ℕ |
    ∃ tree : DecisionTree,
      legalTreeAt (usedCoordinates C) tree ∧
        computesOnCell target C tree ∧ treeDepth tree = d}

def minimumDepthTree
    (target : Cube3 → Bool) (C : Cell3) (tree : DecisionTree) : Prop :=
  legalTreeAt (usedCoordinates C) tree ∧
    computesOnCell target C tree ∧
      treeDepth tree = minimumResidualDepth target C

def locallyMinimumDepthTree
    (target : Cube3 → Bool) (C : Cell3) : DecisionTree → Prop
  | .leaf value => minimumDepthTree target C (.leaf value)
  | .query i ifFalse ifTrue =>
      minimumDepthTree target C (.query i ifFalse ifTrue) ∧
        locallyMinimumDepthTree target (extendCell C i false) ifFalse ∧
          locallyMinimumDepthTree target (extendCell C i true) ifTrue

def remainingWeight (target : Cube3 → Bool) : ℝ :=
  if target = atomH then 1 / 4 else 3 / 4

def remainingRealAtom (target : Cube3 → Bool) : Cube3 → ℝ :=
  if target = atomH then realEll else realH

def remainingBoolAtom (target : Cube3 → Bool) : Cube3 → Bool :=
  if target = atomH then atomEll else atomH

def removedTailTerm (target : Cube3 → Bool) (C : Cell3) (r : ℕ) : ℝ :=
  if minimumResidualDepth (remainingBoolAtom target) C ≥ r + 1 then
    let w := remainingWeight target
    w ^ 2 - (w * cellMean C (remainingRealAtom target)) ^ 2
  else 0

def terminalPotentialAfterRemoving
    (target : Cube3 → Bool) (C : Cell3) : ℝ :=
  ∑ r ∈ Finset.range 3, removedTailTerm target C r

def treeCharge
    (target : Cube3 → Bool) (C : Cell3) : DecisionTree → ℝ
  | .leaf _ => terminalPotentialAfterRemoving target C
  | .query i ifFalse ifTrue =>
      cellVariance C targetG +
        (treeCharge target (extendCell C i false) ifFalse +
          treeCharge target (extendCell C i true) ifTrue) / 2

def minimumCharge (target : Cube3 → Bool) : ℝ :=
  sInf {z : ℝ |
    ∃ tree : DecisionTree,
      locallyMinimumDepthTree target (fun _ => none) tree ∧
        z = treeCharge target (fun _ => none) tree}

def fullTailMass (C : Cell3) (r : ℕ) : ℝ :=
  (if minimumResidualDepth atomH C ≥ r + 1 then (3 / 4 : ℝ) else 0) +
    (if minimumResidualDepth atomEll C ≥ r + 1 then (1 / 4 : ℝ) else 0)

def fullTailMean (C : Cell3) (r : ℕ) : ℝ :=
  (if minimumResidualDepth atomH C ≥ r + 1 then
      (3 / 4 : ℝ) * cellMean C realH else 0) +
    (if minimumResidualDepth atomEll C ≥ r + 1 then
      (1 / 4 : ℝ) * cellMean C realEll else 0)

def fullPotential (C : Cell3) : ℝ :=
  ∑ r ∈ Finset.range 3, (fullTailMass C r ^ 2 - fullTailMean C r ^ 2)

def emptyCell : Cell3 := fun _ => none

/-- The exact finite decision-tree charge statement for the displayed
three-coordinate two-atom law.  All trees, cells, residual depths, and tail
potentials are attached to the concrete masks `139` and `15`; no abstract
function or policy callback is substituted for the stated model. -/
def squaredDepthTailMinimumClaim61165 : Prop :=
  minimumResidualDepth atomH emptyCell = 2 ∧
    minimumResidualDepth atomEll emptyCell = 1 ∧
      cellVariance emptyCell targetG = 13 / 16 ∧
        fullPotential emptyCell = 25 / 16 ∧
          minimumCharge atomH = 53 / 32 ∧
            minimumCharge atomEll = 53 / 32 ∧
              minimumCharge atomH > fullPotential emptyCell ∧
                minimumCharge atomEll > fullPotential emptyCell

end
end MathlibPlus.Open.OracleArea.ConstructivePolicySquaredDepthTailClaim61165
