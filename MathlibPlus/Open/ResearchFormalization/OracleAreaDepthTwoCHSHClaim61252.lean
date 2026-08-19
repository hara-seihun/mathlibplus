import MathlibPlus.Open.ResearchFormalization.RademacherArea

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoCHSHClaim61252

open MathlibPlus.Open.ResearchFormalization
open scoped BigOperators

noncomputable section

def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

def targetFunction (x : RademacherCube 4) : ℝ :=
  -((signValue (x 0) * signValue (x 1) +
      signValue (x 0) * signValue (x 2) +
      signValue (x 1) * signValue (x 3) -
      signValue (x 2) * signValue (x 3)) / 2)

def flipCoordinate (x : RademacherCube 4) (i : Fin 4) :
    RademacherCube 4 :=
  Function.update x i (!(x i))

def walshCoefficient (F : BooleanFunction 4)
    (S : Finset (Fin 4)) : ℝ :=
  uniformMean (fun x =>
    F.1 x * ∏ i : Fin 4, if i ∈ S then signValue (x i) else 1)

def quadraticSupports : Finset (Finset (Fin 4)) :=
  {{0, 1}, {0, 2}, {1, 3}, {2, 3}}

def levelTwoMass (f : RademacherCube 4 → ℝ) : ℝ :=
  (Finset.univ.filter (fun S : Finset (Fin 4) => S.card = 2)).sum
    (fun S =>
      |uniformMean (fun x =>
        f x * ∏ i : Fin 4, if i ∈ S then signValue (x i) else 1)|)

def treeDepth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _ => 0
  | .query _ ifFalse ifTrue =>
      1 + max (treeDepth ifFalse) (treeDepth ifTrue)

def determinesAtDepth (F : BooleanFunction 4) (k : ℕ) : Prop :=
  ∃ tree : DecisionTree 4,
    validDeterminingTree F tree ∧ treeDepth tree ≤ k

def exactMinimumDepthThree (F : BooleanFunction 4) : Prop :=
  (∃ tree : DecisionTree 4,
    validDeterminingTree F tree ∧ treeDepth tree = 3) ∧
  (∀ tree : DecisionTree 4,
    validDeterminingTree F tree → 3 ≤ treeDepth tree)

def depthTwoLaw (law : BooleanLaw 4) : Prop :=
  isProbabilityLaw law ∧
    ∀ entry ∈ law, determinesAtDepth entry.1 2

def lawLevelTwoMass (law : BooleanLaw 4) : ℝ :=
  levelTwoMass (lawBarycenter law)

/-- The exact four-coordinate depth-two obstruction, including the displayed
    Boolean target, Walsh support, pointwise variation, optimal area, and the
    depth-two Boolean-tree-hull bound. -/
def claim61252 : Prop :=
  ∃ F : BooleanFunction 4,
    (∀ x, F.1 x = targetFunction x) ∧
    uniformMean F.1 = 0 ∧
    (∀ S : Finset (Fin 4), S.card ≠ 2 → walshCoefficient F S = 0) ∧
    (∀ S : Finset (Fin 4),
      S.card = 2 →
        (walshCoefficient F S ≠ 0 ↔ S ∈ quadraticSupports)) ∧
    (∀ S ∈ quadraticSupports,
      |walshCoefficient F S| = 1 / 2) ∧
    levelTwoMass F.1 = 2 ∧
    (∀ x, ∑ i : Fin 4,
      |(F.1 x - F.1 (flipCoordinate x i)) / 2| = 2) ∧
    intrinsicArea F = 3 ∧
    exactMinimumDepthThree F ∧
    (∀ law : BooleanLaw 4, depthTwoLaw law → lawLevelTwoMass law ≤ 1)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoCHSHClaim61252
