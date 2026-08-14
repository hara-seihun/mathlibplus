import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

open scoped BigOperators

abbrev RademacherCube (n : ℕ) := Fin n → Bool

noncomputable def BooleanFunction (n : ℕ) :=
  {h : RademacherCube n → ℝ // ∀ x, h x = 1 ∨ h x = -1}

def rademacherValue (b : Bool) : ℝ :=
  if b then 1 else -1

noncomputable def uniformMean {n : ℕ} (g : RademacherCube n → ℝ) : ℝ :=
  (Finset.univ.sum g) / (2 : ℝ) ^ n

inductive DecisionTree (n : ℕ) where
  | leaf (value : ℝ) : DecisionTree n
  | query (coordinate : Fin n) (ifFalse ifTrue : DecisionTree n) : DecisionTree n

def DecisionTree.evaluate {n : ℕ} : DecisionTree n → RademacherCube n → ℝ
  | .leaf value, _ => value
  | .query coordinate ifFalse ifTrue, x =>
      if x coordinate then ifTrue.evaluate x else ifFalse.evaluate x

def DecisionTree.nodePaths {n : ℕ} : DecisionTree n → Finset (List Bool)
  | .leaf _ => {[]}
  | .query _ ifFalse ifTrue =>
      insert []
        ((DecisionTree.nodePaths ifFalse).image (fun path => false :: path) ∪
          (DecisionTree.nodePaths ifTrue).image (fun path => true :: path))

def DecisionTree.queryAt {n : ℕ} : DecisionTree n → List Bool → Option (Fin n)
  | .leaf _, _ => none
  | .query coordinate _ _, [] => some coordinate
  | .query _ ifFalse ifTrue, branch :: path =>
      if branch then ifTrue.queryAt path else ifFalse.queryAt path

/-- A path is a transcript when its branch choices agree with the queried bits. -/
def DecisionTree.follows {n : ℕ} :
    DecisionTree n → RademacherCube n → List Bool → Prop
  | _, _, [] => True
  | .leaf _, _, _ :: _ => False
  | .query coordinate ifFalse ifTrue, x, branch :: path =>
      if x coordinate = branch then
        if branch then ifTrue.follows x path else ifFalse.follows x path
      else False

def DecisionTree.internalPaths {n : ℕ} (tree : DecisionTree n) : Finset (List Bool) :=
  tree.nodePaths.filter (fun path => (tree.queryAt path).isSome)

noncomputable def transcriptCell {n : ℕ} (tree : DecisionTree n)
    (path : List Bool) : Finset (RademacherCube n) := by
  classical
  exact Finset.univ.filter (fun x => tree.follows x path)

noncomputable def conditionalMean {n : ℕ} (h : BooleanFunction n)
    (cell : Finset (RademacherCube n)) : ℝ :=
  (cell.sum h.1) / (cell.card : ℝ)

noncomputable def nodeProbability {n : ℕ} (tree : DecisionTree n)
    (path : List Bool) : ℝ :=
  ((transcriptCell tree path).card : ℝ) / (2 : ℝ) ^ n

noncomputable def nodeMean {n : ℕ} (h : BooleanFunction n)
    (tree : DecisionTree n) (path : List Bool) : ℝ :=
  conditionalMean h (transcriptCell tree path)

noncomputable def nodeHalfDifference {n : ℕ} (h : BooleanFunction n)
    (tree : DecisionTree n) (path : List Bool) : ℝ :=
  (conditionalMean h (transcriptCell tree (path ++ [true])) -
      conditionalMean h (transcriptCell tree (path ++ [false]))) / 2

noncomputable def firstLevelCoefficient {n : ℕ} (h : BooleanFunction n)
    (coordinate : Fin n) : ℝ :=
  uniformMean (fun x => h.1 x * rademacherValue (x coordinate))

noncomputable def nodeContribution {n : ℕ} (h : BooleanFunction n)
    (tree : DecisionTree n) (coordinate : Fin n) : ℝ :=
  (tree.internalPaths.filter (fun path => tree.queryAt path = some coordinate)).sum
    (fun path => nodeProbability tree path * nodeHalfDifference h tree path)

noncomputable def decisionTreeArea {n : ℕ} (h : BooleanFunction n)
    (tree : DecisionTree n) : ℝ :=
  tree.internalPaths.sum (fun path =>
    nodeProbability tree path * (1 - (nodeMean h tree path) ^ 2))

def noRepeatFrom {n : ℕ} (seen : Finset (Fin n)) : DecisionTree n → Prop
  | .leaf _ => True
  | .query coordinate ifFalse ifTrue =>
      coordinate ∉ seen ∧
        noRepeatFrom (insert coordinate seen) ifFalse ∧
        noRepeatFrom (insert coordinate seen) ifTrue

def noRepeat {n : ℕ} (tree : DecisionTree n) : Prop :=
  noRepeatFrom ∅ tree

def determines {n : ℕ} (h : BooleanFunction n) (tree : DecisionTree n) : Prop :=
  ∀ x, tree.evaluate x = h.1 x

def validDeterminingTree {n : ℕ} (h : BooleanFunction n)
    (tree : DecisionTree n) : Prop :=
  noRepeat tree ∧ determines h tree

noncomputable def intrinsicArea {n : ℕ} (h : BooleanFunction n) : ℝ :=
  sInf {a : ℝ | ∃ tree : DecisionTree n,
    validDeterminingTree h tree ∧ a = decisionTreeArea h tree}

noncomputable def firstLevelMass {n : ℕ} (h : BooleanFunction n) : ℝ :=
  (Finset.univ.sum (fun coordinate => |firstLevelCoefficient h coordinate|))

/-- R-3593, record 1, claim 50867. -/
def claim50867 : Prop :=
  ∀ (n : ℕ) (h : BooleanFunction n) (tree : DecisionTree n),
    validDeterminingTree h tree →
      (∀ coordinate, firstLevelCoefficient h coordinate =
        nodeContribution h tree coordinate) ∧
      (∀ path ∈ tree.internalPaths,
        |nodeHalfDifference h tree path| ≤ 1 - (nodeMean h tree path) ^ 2) ∧
      firstLevelMass h ≤ decisionTreeArea h tree ∧
      firstLevelMass h ≤ intrinsicArea h

structure AffineData (n : ℕ) where
  intercept : ℝ
  coefficient : Fin n → ℝ

def affineValue {n : ℕ} (data : AffineData n)
    (x : RademacherCube n) : ℝ :=
  data.intercept + Finset.univ.sum (fun i => data.coefficient i * rademacherValue (x i))

def affineBounded {n : ℕ} (data : AffineData n) : Prop :=
  |data.intercept| + Finset.univ.sum (fun i => |data.coefficient i|) ≤ 1

abbrev BooleanLaw (m : ℕ) := List (BooleanFunction m × ℝ)

def lawWeightSum {m : ℕ} (law : BooleanLaw m) : ℝ :=
  (law.map Prod.snd).sum

def lawNonnegative {m : ℕ} (law : BooleanLaw m) : Prop :=
  ∀ entry ∈ law, 0 ≤ entry.2

def isProbabilityLaw {m : ℕ} (law : BooleanLaw m) : Prop :=
  lawNonnegative law ∧ lawWeightSum law = 1

def lawBarycenter {m : ℕ} (law : BooleanLaw m)
    (x : RademacherCube m) : ℝ :=
  (law.map (fun entry => entry.2 * entry.1.1 x)).sum

noncomputable def restrictCube {n m : ℕ} (hm : n ≤ m)
    (x : RademacherCube m) : RademacherCube n :=
  fun i => x ⟨i.1, lt_of_lt_of_le i.2 hm⟩

def representsAffine {n m : ℕ} (data : AffineData n) (hm : n ≤ m)
    (law : BooleanLaw m) : Prop :=
  isProbabilityLaw law ∧
    ∀ x, lawBarycenter law x = affineValue data (restrictCube hm x)

noncomputable def lawExpectedArea {m : ℕ} (law : BooleanLaw m) : ℝ :=
  (law.map (fun entry => entry.2 * intrinsicArea entry.1)).sum

noncomputable def affineConvexRoof {n : ℕ} (data : AffineData n) : ℝ :=
  sInf {r : ℝ | ∃ (m : ℕ) (hm : n ≤ m) (law : BooleanLaw m),
    representsAffine data hm law ∧ r = lawExpectedArea law}

noncomputable def signedLiteral {n : ℕ} (coordinate : Fin n) (positive : Bool) :
    BooleanFunction n := by
  classical
  refine ⟨(fun x => if positive then rademacherValue (x coordinate)
    else -rademacherValue (x coordinate)), ?_⟩
  intro x
  by_cases hp : positive
  · cases hxc : x coordinate <;> simp [hp, hxc, rademacherValue]
  · cases hxc : x coordinate <;> simp [hp, hxc, rademacherValue]

noncomputable def booleanConstant {n : ℕ} (positive : Bool) : BooleanFunction n := by
  classical
  refine ⟨(fun _ => if positive then (1 : ℝ) else -1), ?_⟩
  intro x
  by_cases hp : positive <;> simp [hp]

noncomputable def coefficientMass {n : ℕ} (data : AffineData n) : ℝ :=
  Finset.univ.sum (fun i => |data.coefficient i|)

noncomputable def canonicalAffineLaw {n : ℕ} (data : AffineData n) : BooleanLaw n := by
  classical
  exact
    (Finset.univ.toList.map (fun i =>
      (signedLiteral i (decide (0 ≤ data.coefficient i)),
        |data.coefficient i|))) ++
      [(booleanConstant true,
        (1 - coefficientMass data + data.intercept) / 2),
       (booleanConstant false,
        (1 - coefficientMass data - data.intercept) / 2)]

/-- R-3593, record 2, claim 50868. -/
def claim50868 : Prop :=
  ∀ (n : ℕ) (data : AffineData n),
    affineBounded data →
      affineConvexRoof data = coefficientMass data ∧
      isProbabilityLaw (canonicalAffineLaw data) ∧
      representsAffine data (Nat.le_refl n) (canonicalAffineLaw data) ∧
      lawExpectedArea (canonicalAffineLaw data) = coefficientMass data

end ResearchFormalization
end Open
end MathlibPlus
