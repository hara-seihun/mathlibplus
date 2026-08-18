import MathlibPlus.Open.ResearchFormalization.RademacherArea
import MathlibPlus.Open.Probability.ResearchBatch

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoOneFifthClaim61216

noncomputable section

abbrev Cube61216 := MathlibPlus.Open.ResearchFormalization.RademacherCube 6

/-- The three fixed depth-at-most-two atom formulas. -/
def h1Formula61216 (x : Cube61216) : ℝ :=
  (rademacherValue (x 3) - rademacherValue (x 5) -
      rademacherValue (x 0) * rademacherValue (x 3) -
      rademacherValue (x 0) * rademacherValue (x 5)) / 2

def h2Formula61216 (x : Cube61216) : ℝ :=
  (rademacherValue (x 1) + rademacherValue (x 2) -
      rademacherValue (x 1) * rademacherValue (x 4) +
      rademacherValue (x 2) * rademacherValue (x 4)) / 2

def h3Formula61216 (x : Cube61216) : ℝ :=
  -rademacherValue (x 5)

def h1Branch61216 (x : Cube61216) : ℝ :=
  if x 0 then -rademacherValue (x 5) else rademacherValue (x 3)

def h2Branch61216 (x : Cube61216) : ℝ :=
  if x 4 then rademacherValue (x 2) else rademacherValue (x 1)

def h3Branch61216 (x : Cube61216) : ℝ :=
  -rademacherValue (x 5)

def literalTree61216 (i : Fin 6) : DecisionTree 6 :=
  .query i (.leaf (-1)) (.leaf 1)

def negativeLiteralTree61216 (i : Fin 6) : DecisionTree 6 :=
  .query i (.leaf 1) (.leaf (-1))

def h1Tree61216 : DecisionTree 6 :=
  .query 0 (literalTree61216 3) (negativeLiteralTree61216 5)

def h2Tree61216 : DecisionTree 6 :=
  .query 4 (literalTree61216 1) (literalTree61216 2)

def h3Tree61216 : DecisionTree 6 :=
  negativeLiteralTree61216 5

def treeDepth61216 {n : ℕ} : DecisionTree n → ℕ
  | .leaf _ => 0
  | .query _ left right => max (treeDepth61216 left) (treeDepth61216 right) + 1

def atomFunction61216 (r : Fin 3) : Cube61216 → ℝ :=
  if r = 0 then h1Formula61216
  else if r = 1 then h2Formula61216
  else h3Formula61216

def atomWeight61216 (r : Fin 3) : ℝ :=
  if r = 0 then 9 / 20
  else if r = 1 then 23 / 50
  else 9 / 100

def mixtureTarget61216 (x : Cube61216) : ℝ :=
  ∑ r : Fin 3, atomWeight61216 r * atomFunction61216 r x

def uniformExpectation61216 (f : Cube61216 → ℝ) : ℝ :=
  uniformMean f

def targetVariance61216 : ℝ :=
  uniformExpectation61216
    (fun x => (mixtureTarget61216 x -
      uniformExpectation61216 mixtureTarget61216) ^ 2)

/-- The finite Walsh characters and coefficients used by the source notation. -/
def walshCharacter61216
    (S : Finset (Fin 6)) (x : Cube61216) : ℝ :=
  ∏ i ∈ S, rademacherValue (x i)

def walshCoefficient61216
    (f : Cube61216 → ℝ) (S : Finset (Fin 6)) : ℝ :=
  uniformExpectation61216 (fun x => f x * walshCharacter61216 S x)

def aCoefficient61216 (r : Fin 3) (i : Fin 6) : ℝ :=
  walshCoefficient61216 (atomFunction61216 r) {i}

def bCoefficient61216 (r : Fin 3) (i j : Fin 6) : ℝ :=
  if i = j then 0 else
    walshCoefficient61216 (atomFunction61216 r) (insert i {j})

def lawAverage61216 (q : Fin 3 → ℝ) : ℝ :=
  ∑ r : Fin 3, atomWeight61216 r * q r

def barACoefficient61216 (i : Fin 6) : ℝ :=
  lawAverage61216 (fun r => aCoefficient61216 r i)

def intrinsicLoad61216 (i : Fin 6) : ℝ :=
  ∑ r : Fin 3, atomWeight61216 r *
    (aCoefficient61216 r i ^ 2 +
      ∑ j ∈ (Finset.univ.filter (fun j : Fin 6 => j ≠ i)),
        |bCoefficient61216 r i j|)

def defect61216 (i j : Fin 6) : ℝ :=
  lawAverage61216 (fun r =>
    |bCoefficient61216 r i j| - bCoefficient61216 r i j ^ 2)

def covarianceCredit61216 (i j : Fin 6) : ℝ :=
  lawAverage61216 (fun r =>
    aCoefficient61216 r j * bCoefficient61216 r i j)

def excludedMaximum61216
    (i : Fin 6) (q : Fin 6 → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ j : Fin 6, j ≠ i ∧ x = q j}

def branchCredit61216 (i : Fin 6) : ℝ :=
  (excludedMaximum61216 i
      (fun j => intrinsicLoad61216 j - defect61216 i j -
        2 * covarianceCredit61216 i j) +
    excludedMaximum61216 i
      (fun j => intrinsicLoad61216 j - defect61216 i j +
        2 * covarianceCredit61216 i j)) / 2

def augmentedScore61216 (i : Fin 6) : ℝ :=
  intrinsicLoad61216 i + barACoefficient61216 i ^ 2 / 5

def staticReveal61216 (i : Fin 6) : Prop :=
  2 * targetVariance61216 - barACoefficient61216 i ^ 2 ≤
    intrinsicLoad61216 i + branchCredit61216 i

def staticMargin61216 (i : Fin 6) : ℝ :=
  intrinsicLoad61216 i + branchCredit61216 i +
      barACoefficient61216 i ^ 2 - 2 * targetVariance61216

def expectedBarA61216 : Fin 6 → ℝ :=
  ![0, 23 / 100, 23 / 100, 9 / 40, 0, -63 / 200]

def expectedLoad61216 : Fin 6 → ℝ :=
  ![9 / 20, 69 / 200, 69 / 200, 27 / 80, 23 / 50, 171 / 400]

def expectedBranchCredit61216 : Fin 6 → ℝ :=
  ![1 / 2, 9 / 20, 9 / 20, 23 / 50, 23 / 50, 23 / 50]

def expectedMargin61216 : Fin 6 → ℝ :=
  ![123 / 5000, -31 / 400, -31 / 400, -3091 / 40000,
    -27 / 5000, 2453 / 40000]

def expectedScore61216 : Fin 6 → ℝ :=
  ![9 / 20, 17779 / 50000, 17779 / 50000, 2781 / 8000,
    23 / 50, 89469 / 200000]

/-- Claim 61216: the exact three-atom augmented-score obstruction, including
legality, all displayed rational data, the failing fourth coordinate, the
surviving zero-coordinate static certificate, and the exact optimal area. -/
def claim61216_augmentedLoadSelectionObstruction : Prop :=
  (∀ x : Cube61216, h1Formula61216 x = h1Branch61216 x) ∧
    (∀ x : Cube61216, h2Formula61216 x = h2Branch61216 x) ∧
    (∀ x : Cube61216, h3Formula61216 x = h3Branch61216 x) ∧
    (∀ x : Cube61216,
      DecisionTree.evaluate h1Tree61216 x = h1Formula61216 x) ∧
    (∀ x : Cube61216,
      DecisionTree.evaluate h2Tree61216 x = h2Formula61216 x) ∧
    (∀ x : Cube61216,
      DecisionTree.evaluate h3Tree61216 x = h3Formula61216 x) ∧
    noRepeat h1Tree61216 ∧ noRepeat h2Tree61216 ∧ noRepeat h3Tree61216 ∧
    treeDepth61216 h1Tree61216 ≤ 2 ∧
    treeDepth61216 h2Tree61216 ≤ 2 ∧
    treeDepth61216 h3Tree61216 ≤ 2 ∧
    (∀ r : Fin 3, ∀ x : Cube61216,
      atomFunction61216 r x = 1 ∨ atomFunction61216 r x = -1) ∧
    targetVariance61216 = 4627 / 10000 ∧
    (∀ i : Fin 6,
      barACoefficient61216 i = expectedBarA61216 i) ∧
    (∀ i : Fin 6,
      intrinsicLoad61216 i = expectedLoad61216 i) ∧
    (∀ i : Fin 6,
      branchCredit61216 i = expectedBranchCredit61216 i) ∧
    (∀ i : Fin 6,
      staticMargin61216 i = expectedMargin61216 i) ∧
    (∀ i : Fin 6,
      augmentedScore61216 i = expectedScore61216 i) ∧
    (∀ i : Fin 6, augmentedScore61216 i ≤ augmentedScore61216 4) ∧
    (∀ i : Fin 6,
      augmentedScore61216 i = augmentedScore61216 4 → i = 4) ∧
    ¬ staticReveal61216 4 ∧
    staticMargin61216 4 = -27 / 5000 ∧
    0 < staticMargin61216 0 ∧
    staticReveal61216 0 ∧
    MathlibPlus.Open.Probability.ResearchBatch.optimalArea
        mixtureTarget61216 = 5443 / 4000 ∧
    MathlibPlus.Open.Probability.ResearchBatch.optimalArea
        mixtureTarget61216 < 2

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoOneFifthClaim61216
