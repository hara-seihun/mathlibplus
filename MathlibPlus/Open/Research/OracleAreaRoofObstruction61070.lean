import Mathlib

namespace MathlibPlus.Open.Research.OracleAreaRoofObstruction

open scoped BigOperators

abbrev BooleanTable (n : ℕ) := Fin (2 ^ n) → Bool
abbrev RealTable (n : ℕ) := Fin (2 ^ n) → ℝ

private def booleanReal (b : Bool) : ℝ :=
  if b then 1 else -1

private def truthIndex (n : ℕ) (x : Fin n → Bool) : Fin (2 ^ n) :=
  Fin.ofNat (2 ^ n) (∑ i : Fin n, if x i then 2 ^ i.1 else 0)

private def tableOfBoolean (n : ℕ) (h : BooleanTable n) : RealTable n :=
  fun i => booleanReal (h i)

inductive CoordinateDecisionTree (n : ℕ) where
  | leaf (value : Bool)
  | query (coordinate : Fin n)
      (negativeBranch positiveBranch : CoordinateDecisionTree n)

private def decisionTreeRun {n : ℕ} :
    CoordinateDecisionTree n → (Fin n → Bool) → Bool
  | CoordinateDecisionTree.leaf value, _ => value
  | CoordinateDecisionTree.query coordinate negativeBranch positiveBranch, x =>
      if x coordinate then
        decisionTreeRun positiveBranch x
      else
        decisionTreeRun negativeBranch x

private def decisionTreeDepth {n : ℕ} :
    CoordinateDecisionTree n → ℕ
  | CoordinateDecisionTree.leaf _ => 0
  | CoordinateDecisionTree.query _ negativeBranch positiveBranch =>
      1 + max (decisionTreeDepth negativeBranch)
        (decisionTreeDepth positiveBranch)

private def decisionTreeRepresents
    (n : ℕ) (tree : CoordinateDecisionTree n) (h : BooleanTable n) : Prop :=
  ∀ x : Fin n → Bool,
    decisionTreeRun tree x = h (truthIndex n x)

private noncomputable def minimumDecisionDepth
    (n : ℕ) (h : BooleanTable n) : ℕ :=
  sInf {d : ℕ |
    ∃ tree : CoordinateDecisionTree n,
      decisionTreeDepth tree = d ∧ decisionTreeRepresents n tree h}

private noncomputable def uniformTableAverage
    (n : ℕ) (f : RealTable n) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ i : Fin (2 ^ n), f i

private noncomputable def tableVariance
    (n : ℕ) (f : RealTable n) : ℝ :=
  let mean := uniformTableAverage n f
  uniformTableAverage n (fun i => (f i - mean) ^ 2)

private noncomputable def BooleanCost
    (n : ℕ) (h : BooleanTable n) : ℝ :=
  Real.sqrt ((minimumDecisionDepth n h : ℝ) * tableVariance n (tableOfBoolean n h))

private def finiteConvexDecomposition
    (n : ℕ) (f : RealTable n) (m : ℕ)
    (weight : Fin m → ℝ) (table : Fin m → BooleanTable n) : Prop :=
  (∀ r : Fin m, 0 ≤ weight r) ∧
    (∑ r : Fin m, weight r = 1) ∧
      (∀ i : Fin (2 ^ n),
        f i = ∑ r : Fin m, weight r * booleanReal (table r i))

private noncomputable def BooleanConvexRoof
    (n : ℕ) (f : RealTable n) : ℝ :=
  sInf {q : ℝ |
    ∃ m : ℕ, ∃ weight : Fin m → ℝ,
      ∃ table : Fin m → BooleanTable n,
        finiteConvexDecomposition n f m weight table ∧
          q = ∑ r : Fin m, weight r * BooleanCost n (table r)}

private def maskTable (n m : ℕ) : BooleanTable n :=
  fun i => Nat.testBit m i.1

private noncomputable def displayedFunction61070 : RealTable 3 :=
  fun i =>
    (4 / 5 : ℝ) * booleanReal (maskTable 3 39 i) +
      (1 / 5 : ℝ) * booleanReal (maskTable 3 219 i)

private noncomputable def displayedVector61070 : RealTable 3 :=
  ![1, 1, 3 / 5, -3 / 5, -3 / 5, 3 / 5, -3 / 5, -3 / 5]

private def insertBit61070
    (i : Fin 3) (b : Bool) (y : Fin 2 → Bool) : Fin 3 → Bool :=
  if i = 0 then
    ![b, y 0, y 1]
  else if i = 1 then
    ![y 0, b, y 1]
  else
    ![y 0, y 1, b]

private noncomputable def childTable61070
    (f : RealTable 3) (i : Fin 3) (b : Bool) : RealTable 2 :=
  fun k =>
    f (truthIndex 3 (insertBit61070 i b
      (fun j : Fin 2 => Nat.testBit k.1 j.1)))

private noncomputable def bellmanRight61070
    (f : RealTable 3) (i : Fin 3) : ℝ :=
  tableVariance 3 f +
    (BooleanConvexRoof 2 (childTable61070 f i false) ^ 2 +
      BooleanConvexRoof 2 (childTable61070 f i true) ^ 2) / 2

private noncomputable def upperRoofValue61070 : ℝ :=
  Real.sqrt 6 / 10 + 3 * Real.sqrt 2 / 5

private noncomputable def coordinateZeroChildValue61070 : ℝ :=
  Real.sqrt 6 / 10 + 3 / 5

private noncomputable def coordinateNegativeChildValue61070 : ℝ :=
  1 / 5 + 3 * Real.sqrt 6 / 10

private noncomputable def coordinatePositiveChildValue61070 : ℝ :=
  3 * Real.sqrt 6 / 10

private noncomputable def firstBellmanRight61070 : ℝ :=
  93 / 100 + 3 * Real.sqrt 6 / 25

private noncomputable def otherBellmanRight61070 : ℝ :=
  107 / 100 + 3 * Real.sqrt 6 / 50

private noncomputable def strictGap61070 : ℝ :=
  (29 + 6 * Real.sqrt 6 - 24 * Real.sqrt 3) / 100

/-- The exact n=3 Boolean convex-roof counterexample, including its finite
three-term upper decomposition, exact two-cube child roofs, and strict
reversal of the proposed Bellman inequality at every first coordinate. -/
def claim61070_squaredBooleanConvexRoofBellmanFailure : Prop :=
  let f := displayedFunction61070
  (∀ i : Fin 8, f i = displayedVector61070 i) ∧
    (∀ i : Fin 8, -1 ≤ f i ∧ f i ≤ 1) ∧
    tableVariance 3 f = 51 / 100 ∧
    (∃ weight : Fin 3 → ℝ, ∃ table : Fin 3 → BooleanTable 3,
      finiteConvexDecomposition 3 f 3 weight table ∧
        weight = ![1 / 5, 3 / 5, 1 / 5] ∧
        table = ![maskTable 3 3, maskTable 3 39, maskTable 3 255] ∧
        (∑ r : Fin 3, weight r * BooleanCost 3 (table r)) ≤
          upperRoofValue61070) ∧
    BooleanConvexRoof 3 f ≤ upperRoofValue61070 ∧
    upperRoofValue61070 ^ 2 =
      39 / 50 + 6 * Real.sqrt 3 / 25 ∧
    (∀ b : Bool,
      BooleanConvexRoof 2 (childTable61070 f 0 b) =
        coordinateZeroChildValue61070) ∧
    ((BooleanConvexRoof 2 (childTable61070 f 1 false) =
        coordinateNegativeChildValue61070 ∧
      BooleanConvexRoof 2 (childTable61070 f 1 true) =
        coordinatePositiveChildValue61070) ∨
      (BooleanConvexRoof 2 (childTable61070 f 1 false) =
        coordinatePositiveChildValue61070 ∧
      BooleanConvexRoof 2 (childTable61070 f 1 true) =
        coordinateNegativeChildValue61070)) ∧
    ((BooleanConvexRoof 2 (childTable61070 f 2 false) =
        coordinateNegativeChildValue61070 ∧
      BooleanConvexRoof 2 (childTable61070 f 2 true) =
        coordinatePositiveChildValue61070) ∨
      (BooleanConvexRoof 2 (childTable61070 f 2 false) =
        coordinatePositiveChildValue61070 ∧
      BooleanConvexRoof 2 (childTable61070 f 2 true) =
        coordinateNegativeChildValue61070)) ∧
    bellmanRight61070 f 0 = firstBellmanRight61070 ∧
    bellmanRight61070 f 1 = otherBellmanRight61070 ∧
    bellmanRight61070 f 2 = otherBellmanRight61070 ∧
    otherBellmanRight61070 < firstBellmanRight61070 ∧
    otherBellmanRight61070 - upperRoofValue61070 ^ 2 = strictGap61070 ∧
    0 < strictGap61070 ∧
    (∀ i : Fin 3,
      bellmanRight61070 f i > BooleanConvexRoof 3 f ^ 2)

end MathlibPlus.Open.Research.OracleAreaRoofObstruction
