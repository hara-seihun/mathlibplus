import Mathlib
import MathlibPlus.Open.ResearchFormalization.RademacherArea
import MathlibPlus.Open.OracleArea.DepthTwoRoofObstruction

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Claim61207SquareRootPotentialObstruction

open Filter Set Topology Classical

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev Transcript (n : ℕ) := Fin n → Option Bool
abbrev RealTarget (n : ℕ) := Cube n → ℝ
abbrev RealTree (n : ℕ) :=
  MathlibPlus.Open.ResearchFormalization.DecisionTree n

private def transcriptConsistent {n : ℕ}
    (τ : Transcript n) (x : Cube n) : Prop :=
  ∀ i : Fin n, ∀ b : Bool, τ i = some b → x i = b

private def assignedCoordinates {n : ℕ}
    (τ : Transcript n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (τ i).isSome)

private noncomputable def transcriptCell {n : ℕ}
    (τ : Transcript n) : Finset (Cube n) :=
  Finset.univ.filter (transcriptConsistent τ)

private def freshFrom {n : ℕ} (seen : Finset (Fin n)) :
    RealTree n → Prop
  | MathlibPlus.Open.ResearchFormalization.DecisionTree.leaf _ => True
  | MathlibPlus.Open.ResearchFormalization.DecisionTree.query i left right =>
      i ∉ seen ∧
        freshFrom (insert i seen) left ∧
          freshFrom (insert i seen) right

private def freshTree {n : ℕ} (τ : Transcript n) (tree : RealTree n) : Prop :=
  freshFrom (assignedCoordinates τ) tree

private noncomputable def conditionalMean {n : ℕ}
    (f : RealTarget n) (cell : Finset (Cube n)) : ℝ :=
  cell.sum f / (cell.card : ℝ)

private noncomputable def conditionalVariance {n : ℕ}
    (f : RealTarget n) (cell : Finset (Cube n)) : ℝ :=
  cell.sum (fun x =>
      (f x - conditionalMean f cell) ^ 2) / (cell.card : ℝ)

private noncomputable def realTreeArea {n : ℕ}
    (τ : Transcript n) (f : RealTarget n) (tree : RealTree n) : ℝ :=
  let rootCell := transcriptCell τ
  (MathlibPlus.Open.ResearchFormalization.DecisionTree.internalPaths tree).sum
    (fun path =>
      let cell :=
        rootCell ∩
          MathlibPlus.Open.ResearchFormalization.transcriptCell tree path
      (cell.card : ℝ) / (rootCell.card : ℝ) *
        conditionalVariance f cell)

private noncomputable def areaAt {n : ℕ}
    (τ : Transcript n) (f : RealTarget n) : ℝ :=
  sInf {a : ℝ |
    ∃ tree : RealTree n,
      freshTree τ tree ∧
        (∀ x ∈ transcriptCell τ, tree.evaluate x = f x) ∧
          a = realTreeArea τ f tree}

private def emptyTranscript {n : ℕ} : Transcript n :=
  fun _ => none

private def childTranscript {n : ℕ}
    (τ : Transcript n) (i : Fin n) (b : Bool) : Transcript n :=
  Function.update τ i (some b)

private noncomputable def childAreaAverage {n : ℕ}
    (τ : Transcript n) (f : RealTarget n) (i : Fin n) : ℝ :=
  (areaAt (childTranscript τ i false) f +
      areaAt (childTranscript τ i true) f) / 2

private noncomputable def bellmanMinimum {n : ℕ}
    (τ : Transcript n) (f : RealTarget n) : ℝ :=
  sInf {a : ℝ | ∃ i : Fin n, a = childAreaAverage τ f i}

private def isConstant {n : ℕ} (f : RealTarget n) : Prop :=
  ∀ x y : Cube n, f x = f y

private noncomputable def rootVariance {n : ℕ}
    (f : RealTarget n) : ℝ :=
  conditionalVariance f (transcriptCell (emptyTranscript : Transcript n))

private def bellmanRecursion61207 : Prop :=
  ∀ (n : ℕ) (f : RealTarget n),
    (isConstant f → areaAt (emptyTranscript : Transcript n) f = 0) ∧
      (¬ isConstant f →
        areaAt (emptyTranscript : Transcript n) f =
          rootVariance f +
            bellmanMinimum (emptyTranscript : Transcript n) f)

private def littleEndianCube (j : Fin 8) : Cube 3 :=
  fun i => decide (((j.1 / 2 ^ i.1) % 2) = 1)

private def table3LE {α : Type*}
    (values : Fin 8 → α) (x : Cube 3) : α :=
  if x 0 then
    if x 1 then
      if x 2 then values 7 else values 3
    else if x 2 then values 5 else values 1
  else if x 1 then
    if x 2 then values 6 else values 2
  else if x 2 then values 4 else values 0

private def booleanTable3LE (values : Fin 8 → Bool) :
    MathlibPlus.Open.OracleArea.BooleanFunction 3 :=
  table3LE values

private def hBoolean :
    MathlibPlus.Open.OracleArea.BooleanFunction 3 :=
  booleanTable3LE ![true, true, false, false, true, false, true, false]

private def ellBoolean :
    MathlibPlus.Open.OracleArea.BooleanFunction 3 :=
  booleanTable3LE ![true, true, false, false, true, false, false, false]

private def hReal : RealTarget 3 :=
  MathlibPlus.Open.OracleArea.targetOfBoolean hBoolean

private def ellReal : RealTarget 3 :=
  MathlibPlus.Open.OracleArea.targetOfBoolean ellBoolean

private def gReal : RealTarget 3 :=
  fun x => (4 / 5 : ℝ) * hReal x + (1 / 5 : ℝ) * ellReal x

private def hTable : Fin 8 → ℝ :=
  ![(1 : ℝ), 1, -1, -1, 1, -1, 1, -1]

private def ellTable : Fin 8 → ℝ :=
  ![(1 : ℝ), 1, -1, -1, 1, -1, -1, -1]

private def gTable : Fin 8 → ℝ :=
  ![(1 : ℝ), 1, -1, -1, 1, -1, (3 / 5 : ℝ), -1]

private noncomputable def potential (τ : Transcript 3) : ℝ :=
  ((4 / 5 : ℝ) * Real.sqrt (areaAt τ hReal) +
      (1 / 5 : ℝ) * Real.sqrt (areaAt τ ellReal)) ^ 2

private noncomputable def childPotentialAverage (τ : Transcript 3)
    (i : Fin 3) : ℝ :=
  (potential (childTranscript τ i false) +
      potential (childTranscript τ i true)) / 2

private noncomputable def dropAt (τ : Transcript 3) (i : Fin 3) : ℝ :=
  potential τ - childPotentialAverage τ i

private noncomputable def maximumDrop (τ : Transcript 3) : ℝ :=
  sSup {r : ℝ | ∃ i : Fin 3, r = dropAt τ i}

private def fixedRepresentationBellman61207 : Prop :=
  ∀ τ : Transcript 3,
    conditionalVariance gReal (transcriptCell τ) ≤ maximumDrop τ

/-- Claim 61207: the exact two-atom Boolean-area witness has the displayed
Bellman areas, square-root potential, child potentials, drops, and positive
root defect.  Its fixed representation potential consequently fails the
universal one-step Bellman inequality. -/
def claim61207 : Prop :=
  bellmanRecursion61207 ∧
    (∀ j : Fin 8,
      hReal (littleEndianCube j) = hTable j ∧
        ellReal (littleEndianCube j) = ellTable j ∧
        gReal (littleEndianCube j) = gTable j) ∧
    MathlibPlus.Open.OracleArea.decisionDepth hBoolean = 2 ∧
      MathlibPlus.Open.OracleArea.decisionDepth ellBoolean = 3 ∧
        areaAt (emptyTranscript : Transcript 3) hReal = 2 ∧
          areaAt (emptyTranscript : Transcript 3) ellReal = 25 / 16 ∧
            areaAt (emptyTranscript : Transcript 3) gReal = 737 / 400 ∧
              (areaAt
                  (childTranscript (emptyTranscript : Transcript 3) 0 false)
                  hReal = 5 / 4 ∧
                areaAt
                    (childTranscript (emptyTranscript : Transcript 3) 0 true)
                    hReal = 5 / 4 ∧
                  areaAt
                      (childTranscript (emptyTranscript : Transcript 3) 1 false)
                      hReal = 5 / 4 ∧
                    areaAt
                        (childTranscript
                          (emptyTranscript : Transcript 3) 1 true) hReal =
                      5 / 4 ∧
                      areaAt
                          (childTranscript
                            (emptyTranscript : Transcript 3) 2 false) hReal =
                        1 ∧
                        areaAt
                            (childTranscript
                              (emptyTranscript : Transcript 3) 2 true) hReal =
                          1) ∧
              (areaAt
                  (childTranscript (emptyTranscript : Transcript 3) 0 false)
                  ellReal = 1 ∧
                areaAt
                    (childTranscript (emptyTranscript : Transcript 3) 0 true)
                    ellReal = 5 / 4 ∧
                  areaAt
                      (childTranscript (emptyTranscript : Transcript 3) 1 false)
                      ellReal = 5 / 4 ∧
                    areaAt
                        (childTranscript
                          (emptyTranscript : Transcript 3) 1 true) ellReal =
                      0 ∧
                      areaAt
                          (childTranscript
                            (emptyTranscript : Transcript 3) 2 false) ellReal =
                        1 ∧
                        areaAt
                            (childTranscript
                              (emptyTranscript : Transcript 3) 2 true) ellReal =
                          5 / 4) ∧
              rootVariance gReal = 367 / 400 ∧
                potential (emptyTranscript : Transcript 3) ≤
                    (4 / 5 : ℝ) * areaAt
                        (emptyTranscript : Transcript 3) hReal +
                      (1 / 5 : ℝ) * areaAt
                        (emptyTranscript : Transcript 3) ellReal ∧
                  (4 / 5 : ℝ) * areaAt
                        (emptyTranscript : Transcript 3) hReal +
                      (1 / 5 : ℝ) * areaAt
                        (emptyTranscript : Transcript 3) ellReal =
                    153 / 80 ∧
                    (153 / 80 : ℝ) < 2 ∧ (2 : ℝ) < 3 ∧
                      potential (emptyTranscript : Transcript 3) =
                        537 / 400 + 2 * Real.sqrt 2 / 5 ∧
                        (childPotentialAverage
                            (emptyTranscript : Transcript 3) 0 =
                          209 / 200 + 2 * Real.sqrt 5 / 25 ∧
                          childPotentialAverage
                              (emptyTranscript : Transcript 3) 1 =
                            41 / 40 ∧
                            childPotentialAverage
                                (emptyTranscript : Transcript 3) 2 =
                              169 / 200 + 2 * Real.sqrt 5 / 25) ∧
                          (dropAt
                                (emptyTranscript : Transcript 3) 0 =
                              119 / 400 + 2 * Real.sqrt 2 / 5 -
                                2 * Real.sqrt 5 / 25 ∧
                            dropAt
                                (emptyTranscript : Transcript 3) 1 =
                              127 / 400 + 2 * Real.sqrt 2 / 5 ∧
                              dropAt
                                  (emptyTranscript : Transcript 3) 2 =
                                199 / 400 + 2 * Real.sqrt 2 / 5 -
                                  2 * Real.sqrt 5 / 25) ∧
                            (dropAt
                                  (emptyTranscript : Transcript 3) 2 >
                                dropAt
                                  (emptyTranscript : Transcript 3) 0 ∧
                              dropAt
                                  (emptyTranscript : Transcript 3) 2 >
                                dropAt
                                  (emptyTranscript : Transcript 3) 1 ∧
                                rootVariance gReal -
                                      dropAt
                                        (emptyTranscript : Transcript 3) 2 =
                                    21 / 50 + 2 * Real.sqrt 5 / 25 -
                                      2 * Real.sqrt 2 / 5 ∧
                                  0 <
                                    21 / 50 + 2 * Real.sqrt 5 / 25 -
                                      2 * Real.sqrt 2 / 5) ∧
                              ¬ fixedRepresentationBellman61207

end MathlibPlus.Open.ResearchFormalization.Claim61207SquareRootPotentialObstruction
