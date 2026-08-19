import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim61328

noncomputable section

open Classical

abbrev Cube61328 (n : ℕ) := Fin n → Bool

def signValue61328 (b : Bool) : ℝ :=
  if b then 1 else -1

inductive Tree61328 (n : ℕ) where
  | leaf (value : Bool)
  | query (coordinate : Fin n) (negative positive : Tree61328 n)
  deriving DecidableEq

def evaluate61328 {n : ℕ} : Tree61328 n → Cube61328 n → Bool
  | .leaf value, _ => value
  | .query coordinate negative positive, x =>
      if x coordinate then evaluate61328 positive x else evaluate61328 negative x

def treeDepth61328 {n : ℕ} : Tree61328 n → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max (treeDepth61328 negative) (treeDepth61328 positive)

def noRepeatFrom61328 {n : ℕ} (used : Finset (Fin n)) :
    Tree61328 n → Prop
  | .leaf _ => True
  | .query coordinate negative positive =>
      coordinate ∉ used ∧
        noRepeatFrom61328 (insert coordinate used) negative ∧
          noRepeatFrom61328 (insert coordinate used) positive

def legalTree61328 {n : ℕ} (tree : Tree61328 n) : Prop :=
  noRepeatFrom61328 ∅ tree

def queriedCoordinates61328 {n : ℕ} (tree : Tree61328 n)
    (x : Cube61328 n) : Finset (Fin n) :=
  Tree61328.rec
    (motive := fun _ => Cube61328 n → Finset (Fin n))
    (fun _ => fun _ => ∅)
    (fun coordinate negative positive negativeResult positiveResult =>
      fun y =>
        insert coordinate
          (if y coordinate then positiveResult y else negativeResult y))
    tree x

def pathLength61328 {n : ℕ} (tree : Tree61328 n)
    (x : Cube61328 n) : ℕ :=
  Tree61328.rec
    (motive := fun _ => Cube61328 n → ℕ)
    (fun _ => fun _ => 0)
    (fun coordinate negative positive negativeResult positiveResult =>
      fun y =>
        1 + (if y coordinate then positiveResult y else negativeResult y))
    tree x

def treeValue61328 {n : ℕ} (tree : Tree61328 n)
    (x : Cube61328 n) : ℝ :=
  signValue61328 (evaluate61328 tree x)

def computes61328 {n : ℕ} (tree : Tree61328 n)
    (target : Cube61328 n → Bool) : Prop :=
  ∀ x, evaluate61328 tree x = target x

def nonconstantBool61328 {n : ℕ} (target : Cube61328 n → Bool) : Prop :=
  ∃ x y, target x ≠ target y

def uniformAverage61328 {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

def variance61328 {n : ℕ} (target : Cube61328 n → ℝ) : ℝ :=
  let mean := uniformAverage61328 target
  uniformAverage61328 (fun x => (target x - mean) ^ 2)

def expectedQueries61328 {n : ℕ} (tree : Tree61328 n) : ℝ :=
  uniformAverage61328 (fun x => (pathLength61328 tree x : ℝ))

def minimumExpectedQueryCost61328 {n : ℕ}
    (target : Cube61328 n → Bool) : ℝ :=
  sInf {c : ℝ |
    ∃ tree : Tree61328 n,
      legalTree61328 tree ∧ computes61328 tree target ∧
        expectedQueries61328 tree = c}

def expectedQueryOptimal61328 {n : ℕ}
    (tree : Tree61328 n) : Prop :=
  legalTree61328 tree ∧
    expectedQueries61328 tree =
      minimumExpectedQueryCost61328
        (fun x => evaluate61328 tree x)

def insertSign61328 {n : ℕ} (coordinate : Fin (n + 1))
    (value : Bool) (x : Cube61328 n) : Cube61328 (n + 1) :=
  Fin.insertNth coordinate value x

def restrictTarget61328 {n : ℕ}
    (target : Cube61328 (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) (value : Bool) :
    Cube61328 n → ℝ :=
  fun x => target (insertSign61328 coordinate value x)

def restrictTree61328 {n : ℕ} (tree : Tree61328 n)
    (revealed : Fin n) (value : Bool) : Tree61328 n :=
  Tree61328.rec
    (motive := fun _ => Tree61328 n)
    (fun leafValue => .leaf leafValue)
    (fun coordinate negative positive negativeResult positiveResult =>
      if coordinate = revealed then
        if value then positiveResult else negativeResult
      else
        .query coordinate negativeResult positiveResult)
    tree

def isConstantReal61328 {n : ℕ} (target : Cube61328 n → ℝ) : Prop :=
  ∃ c, ∀ x, target x = c

noncomputable def intrinsicArea61328 :
    (n : ℕ) → (Cube61328 n → ℝ) → ℝ
  | 0, target =>
      if isConstantReal61328 target then 0 else variance61328 target
  | n + 1, target =>
      if isConstantReal61328 target then 0 else
        variance61328 target +
          sInf (Set.range (fun coordinate : Fin (n + 1) =>
            (intrinsicArea61328 n
                (restrictTarget61328 target coordinate false) +
              intrinsicArea61328 n
                (restrictTarget61328 target coordinate true)) / 2))

structure Law61328 (n m : ℕ) where
  weight : Fin m → ℝ
  tree : Fin m → Tree61328 n

def probabilityLaw61328 {n m : ℕ} (law : Law61328 n m) : Prop :=
  (∀ j, 0 ≤ law.weight j) ∧
    ∑ j, law.weight j = 1

def legalLaw61328 {n m : ℕ} (law : Law61328 n m)
    (k : ℕ) : Prop :=
  ∀ j, legalTree61328 (law.tree j) ∧
    treeDepth61328 (law.tree j) ≤ k

def mixtureTarget61328 {n m : ℕ} (law : Law61328 n m) :
    Cube61328 n → ℝ :=
  fun x => ∑ j, law.weight j * treeValue61328 (law.tree j) x

def levelMass61328 {n m : ℕ} (law : Law61328 n m)
    (level : ℕ) : ℝ :=
  uniformAverage61328 (fun x =>
    ∑ j, law.weight j *
      (if level ≤ pathLength61328 (law.tree j) x then 1 else 0))

def profile61328 {n m k : ℕ} (law : Law61328 n m) :
    Fin k → ℝ :=
  fun level => levelMass61328 law (level.val + 1)

def restrictLaw61328 {n m : ℕ} (law : Law61328 n m)
    (coordinate : Fin n) (value : Bool) : Law61328 n m :=
  { weight := law.weight
    tree := fun j =>
      restrictTree61328 (law.tree j) coordinate value }

def profile2Of61328 {n m : ℕ} (law : Law61328 n m) :
    Fin 2 → ℝ :=
  ![levelMass61328 law 1, levelMass61328 law 2]

def reserve61328 (phi : ℝ → ℝ) {n m : ℕ}
    (law : Law61328 n m) (k : ℕ) : ℝ :=
  ∑ level ∈ Finset.range k, phi (levelMass61328 law (level + 1))

def reserveDrop61328 (phi : ℝ → ℝ)
    {n m : ℕ} (law : Law61328 n m)
    (coordinate : Fin n) (k : ℕ) : ℝ :=
  reserve61328 phi law k -
    (reserve61328 phi (restrictLaw61328 law coordinate false) k +
      reserve61328 phi (restrictLaw61328 law coordinate true) k) / 2

def bellmanStep61328 (phi : ℝ → ℝ)
    {n m : ℕ} (law : Law61328 n m)
    (coordinate : Fin n) (k : ℕ) : Prop :=
  variance61328 (mixtureTarget61328 law) +
      (reserve61328 phi
          (restrictLaw61328 law coordinate false) k +
        reserve61328 phi
          (restrictLaw61328 law coordinate true) k) / 2 ≤
    reserve61328 phi law k

def normalizedPhi61328 (phi : ℝ → ℝ) : Prop :=
  0 ≤ phi 0 ∧ phi 1 ≤ 1

def depthTwoLevelMassSupersolution61328 (phi : ℝ → ℝ) : Prop :=
  ∀ (n m : ℕ) (law : Law61328 n m),
    probabilityLaw61328 law →
    legalLaw61328 law 2 →
    0 < variance61328 (mixtureTarget61328 law) →
    ∃ coordinate : Fin n,
      bellmanStep61328 phi law coordinate 2

def noSeparableLevelMassReserve61328 : Prop :=
  ¬ ∃ phi : ℝ → ℝ,
    normalizedPhi61328 phi ∧
      depthTwoLevelMassSupersolution61328 phi

def literalTree61328 {n : ℕ} (coordinate : Fin n) :
    Tree61328 n :=
  .query coordinate (.leaf false) (.leaf true)

def literalConstantLaw61328 (n j : ℕ) : Law61328 n n :=
  { weight := fun _ => 1 / (n : ℝ)
    tree := fun index =>
      if index.val < n - j then
        literalTree61328 index
      else
        .leaf true }

def forcedLiteralLevelInequalities61328 (phi : ℝ → ℝ) : Prop :=
  ∀ (n j : ℕ), 1 ≤ n → j < n →
    phi ((n - j : ℕ) / (n : ℝ)) -
        phi ((n - j - 1 : ℕ) / (n : ℝ)) ≥
      (n - j : ℕ) / (n : ℝ) ^ 2

def forcedPhiConstraints61328 (phi : ℝ → ℝ) : Prop :=
  normalizedPhi61328 phi ∧
    forcedLiteralLevelInequalities61328 phi ∧
    phi (9 / 22) ≥ 81 / 484

def singleLiteralLaw61328 : Law61328 1 2 :=
  { weight := ![(9 : ℝ) / 22, (13 : ℝ) / 22]
    tree := ![literalTree61328 (0 : Fin 1), .leaf true] }

def literalChainCertificate61328 : Prop :=
  ∀ (n j : ℕ), 1 ≤ n → j < n →
    probabilityLaw61328 (literalConstantLaw61328 n j) ∧
      legalLaw61328 (literalConstantLaw61328 n j) 2 ∧
      levelMass61328 (literalConstantLaw61328 n j) 1 =
        (n - j : ℕ) / (n : ℝ) ∧
      levelMass61328 (literalConstantLaw61328 n j) 2 = 0 ∧
      variance61328
          (mixtureTarget61328 (literalConstantLaw61328 n j)) =
        (n - j : ℕ) / (n : ℝ) ^ 2 ∧
      (∀ (coordinate : Fin n), coordinate.val < n - j →
        ∀ value : Bool,
          profile2Of61328
              (restrictLaw61328 (literalConstantLaw61328 n j)
                coordinate value) =
            ![((n - j - 1 : ℕ) / (n : ℝ)), 0])

def singleLiteralCertificate61328 : Prop :=
  probabilityLaw61328 singleLiteralLaw61328 ∧
    legalLaw61328 singleLiteralLaw61328 2 ∧
    profile2Of61328 singleLiteralLaw61328 =
      ![(9 : ℝ) / 22, 0] ∧
    variance61328 (mixtureTarget61328 singleLiteralLaw61328) =
      81 / 484 ∧
    (∀ value : Bool,
      profile2Of61328
        (restrictLaw61328 singleLiteralLaw61328 (0 : Fin 1) value) =
        ![(0 : ℝ), 0])

def treeW1First61328 : Tree61328 4 :=
  .query 2
    (.query 3 (.leaf true) (.leaf false))
    (.query 1 (.leaf true) (.leaf false))

def treeW1Second61328 : Tree61328 4 :=
  .query 3 (.leaf true) (.leaf false)

def lawW1_61328 : Law61328 4 2 :=
  { weight := ![(9 : ℝ) / 11, (2 : ℝ) / 11]
    tree := ![treeW1First61328, treeW1Second61328] }

def profile2W1_61328 : Fin 2 → ℝ :=
  ![levelMass61328 lawW1_61328 1,
    levelMass61328 lawW1_61328 2]

def targetW1Formula61328 (x : Cube61328 4) : ℝ :=
  -(9 / 22 : ℝ) * signValue61328 (x 1) -
      (13 / 22 : ℝ) * signValue61328 (x 3) +
      (9 / 22 : ℝ) * signValue61328 (x 2) *
        signValue61328 (x 3) -
      (9 / 22 : ℝ) * signValue61328 (x 1) *
        signValue61328 (x 2)

def witnessW1_61328 : Prop :=
  probabilityLaw61328 lawW1_61328 ∧
    legalLaw61328 lawW1_61328 2 ∧
    treeDepth61328 treeW1First61328 = 2 ∧
    treeDepth61328 treeW1Second61328 = 1 ∧
    (∀ x, mixtureTarget61328 lawW1_61328 x =
      targetW1Formula61328 x) ∧
    variance61328 (mixtureTarget61328 lawW1_61328) =
      103 / 121 ∧
    profile2W1_61328 = ![(1 : ℝ), 9 / 11] ∧
    expectedQueryOptimal61328 treeW1First61328 ∧
    expectedQueryOptimal61328 treeW1Second61328 ∧
    (∀ (j : Fin 2) (coordinate : Fin 4) (value : Bool),
      nonconstantBool61328
        (fun x => evaluate61328
          (restrictTree61328 (lawW1_61328.tree j) coordinate value) x) →
      expectedQueryOptimal61328
        (restrictTree61328 (lawW1_61328.tree j) coordinate value)) ∧
    (∀ value : Bool,
      profile61328
        (restrictLaw61328 lawW1_61328 (2 : Fin 4) value) =
        ![(1 : ℝ), 0]) ∧
    (∀ value : Bool,
      profile61328
        (restrictLaw61328 lawW1_61328 (1 : Fin 4) value) =
        ![(1 : ℝ), 9 / 22]) ∧
    (∀ value : Bool,
      profile61328
        (restrictLaw61328 lawW1_61328 (3 : Fin 4) value) =
        ![9 / 11, 9 / 22]) ∧
    intrinsicArea61328 4 (mixtureTarget61328 lawW1_61328) =
      817 / 484 ∧
    intrinsicArea61328 4 (mixtureTarget61328 lawW1_61328) < 2

def exactForcedEndpointBounds61328 : Prop :=
  ∀ phi : ℝ → ℝ,
    forcedPhiConstraints61328 phi →
      phi (9 / 11) ≤ 100 / 121 ∧
        phi (9 / 22) ≥ 81 / 484

def exactLevelMassDropBounds61328 : Prop :=
  ∀ phi : ℝ → ℝ,
    forcedPhiConstraints61328 phi →
      reserveDrop61328 phi lawW1_61328 (2 : Fin 4) 2 ≤
          400 / 484 ∧
        reserveDrop61328 phi lawW1_61328 (1 : Fin 4) 2 ≤
          319 / 484 ∧
        reserveDrop61328 phi lawW1_61328 (3 : Fin 4) 2 ≤
          403 / 484 ∧
        reserveDrop61328 phi lawW1_61328 (0 : Fin 4) 2 = 0

def varianceAndObstructionW1_61328 : Prop :=
  variance61328 (mixtureTarget61328 lawW1_61328) =
      412 / 484 ∧
    exactLevelMassDropBounds61328 ∧
    (∀ phi : ℝ → ℝ,
      forcedPhiConstraints61328 phi →
        reserveDrop61328 phi lawW1_61328 (2 : Fin 4) 2 <
            variance61328 (mixtureTarget61328 lawW1_61328) ∧
          reserveDrop61328 phi lawW1_61328 (1 : Fin 4) 2 <
            variance61328 (mixtureTarget61328 lawW1_61328) ∧
          reserveDrop61328 phi lawW1_61328 (3 : Fin 4) 2 <
            variance61328 (mixtureTarget61328 lawW1_61328))

def treeW2_61328 : Tree61328 3 :=
  .query 0 (.leaf true)
    (.query 1
      (.query 2 (.leaf true) (.leaf false))
      (.query 2 (.leaf false) (.leaf true)))

def targetW2_61328 (x : Cube61328 3) : Bool :=
  if x 0 then x 1 = x 2 else true

def lawW2_61328 : Law61328 3 1 :=
  { weight := ![(1 : ℝ)]
    tree := ![treeW2_61328] }

def profile3W2_61328 : Fin 3 → ℝ :=
  ![levelMass61328 lawW2_61328 1,
    levelMass61328 lawW2_61328 2,
    levelMass61328 lawW2_61328 3]

def pairReserveW2_61328 (tree : Tree61328 3) : ℝ :=
  ∑ level ∈ Finset.range 3,
    (uniformAverage61328 (fun x =>
      if level + 1 ≤ pathLength61328 tree x then 1 else 0)) ^ 2

def reducedTree61328 {n : ℕ} : Tree61328 n → Prop
  | .leaf _ => True
  | .query _ negative positive =>
      negative ≠ positive ∧
        reducedTree61328 negative ∧ reducedTree61328 positive

def enumTreeW2_0 : Tree61328 3 := treeW2_61328

def enumTreeW2_1 : Tree61328 3 :=
  .query 0 (.leaf true)
    (.query 2
      (.query 1 (.leaf true) (.leaf false))
      (.query 1 (.leaf false) (.leaf true)))

def enumTreeW2_2 : Tree61328 3 :=
  .query 1
    (.query 0 (.leaf true)
      (.query 2 (.leaf true) (.leaf false)))
    (.query 0 (.leaf true)
      (.query 2 (.leaf false) (.leaf true)))

def enumTreeW2_3 : Tree61328 3 :=
  .query 1
    (.query 0 (.leaf true)
      (.query 2 (.leaf true) (.leaf false)))
    (.query 2
      (.query 0 (.leaf true) (.leaf false))
      (.leaf true))

def enumTreeW2_4 : Tree61328 3 :=
  .query 1
    (.query 2 (.leaf true)
      (.query 0 (.leaf true) (.leaf false)))
    (.query 0 (.leaf true)
      (.query 2 (.leaf false) (.leaf true)))

def enumTreeW2_5 : Tree61328 3 :=
  .query 1
    (.query 2 (.leaf true)
      (.query 0 (.leaf true) (.leaf false)))
    (.query 2
      (.query 0 (.leaf true) (.leaf false))
      (.leaf true))

def enumTreeW2_6 : Tree61328 3 :=
  .query 2
    (.query 0 (.leaf true)
      (.query 1 (.leaf true) (.leaf false)))
    (.query 0 (.leaf true)
      (.query 1 (.leaf false) (.leaf true)))

def enumTreeW2_7 : Tree61328 3 :=
  .query 2
    (.query 0 (.leaf true)
      (.query 1 (.leaf true) (.leaf false)))
    (.query 1
      (.query 0 (.leaf true) (.leaf false))
      (.leaf true))

def enumTreeW2_8 : Tree61328 3 :=
  .query 2
    (.query 1 (.leaf true)
      (.query 0 (.leaf true) (.leaf false)))
    (.query 0 (.leaf true)
      (.query 1 (.leaf false) (.leaf true)))

def enumTreeW2_9 : Tree61328 3 :=
  .query 2
    (.query 1 (.leaf true)
      (.query 0 (.leaf true) (.leaf false)))
    (.query 1
      (.query 0 (.leaf true) (.leaf false))
      (.leaf true))

def enumeratedTreesW2_61328 : List (Tree61328 3) :=
  [enumTreeW2_0, enumTreeW2_1, enumTreeW2_2, enumTreeW2_3,
    enumTreeW2_4, enumTreeW2_5, enumTreeW2_6, enumTreeW2_7,
    enumTreeW2_8, enumTreeW2_9]

def enumerationW2_61328 : Prop :=
  enumeratedTreesW2_61328.length = 10 ∧
    (∀ tree : Tree61328 3,
      legalTree61328 tree ∧ reducedTree61328 tree ∧
          computes61328 tree targetW2_61328 ↔
        tree ∈ enumeratedTreesW2_61328) ∧
    (∀ tree : Tree61328 3,
      tree ∈ enumeratedTreesW2_61328 →
        (expectedQueries61328 tree = 2 ∧
            pairReserveW2_61328 tree = 3 / 2) ∨
          (expectedQueries61328 tree = 5 / 2 ∧
            pairReserveW2_61328 tree = 9 / 4)) ∧
    (∀ tree : Tree61328 3,
      tree ∈ enumeratedTreesW2_61328 →
        (expectedQueries61328 tree = 2 ↔
          tree = enumTreeW2_0 ∨ tree = enumTreeW2_1))

def witnessW2_61328 : Prop :=
  probabilityLaw61328 lawW2_61328 ∧
    legalLaw61328 lawW2_61328 3 ∧
    computes61328 treeW2_61328 targetW2_61328 ∧
    treeDepth61328 treeW2_61328 = 3 ∧
    (∀ x, targetW2_61328 x =
      (if x 0 then x 1 = x 2 else true)) ∧
    profile3W2_61328 = ![(1 : ℝ), 1 / 2, 1 / 2] ∧
    expectedQueries61328 treeW2_61328 = 2 ∧
    pairReserveW2_61328 treeW2_61328 = 3 / 2 ∧
    minimumExpectedQueryCost61328 targetW2_61328 = 2 ∧
    expectedQueryOptimal61328 treeW2_61328 ∧
    intrinsicArea61328 3 (mixtureTarget61328 lawW2_61328) =
      7 / 4 ∧
    intrinsicArea61328 3 (mixtureTarget61328 lawW2_61328) >
      pairReserveW2_61328 treeW2_61328 ∧
    intrinsicArea61328 3 (mixtureTarget61328 lawW2_61328) ≤ 3 ∧
    enumerationW2_61328

def treeW4First61328 : Tree61328 4 :=
  .query 0
    (.query 2 (.leaf false) (.leaf true))
    (.query 1 (.leaf true) (.leaf false))

def treeW4Second61328 : Tree61328 4 :=
  .query 3
    (.query 2 (.leaf false) (.leaf true))
    (.query 1 (.leaf true) (.leaf false))

def lawW4_61328 : Law61328 4 2 :=
  { weight := ![(1 : ℝ) / 2, (1 : ℝ) / 2]
    tree := ![treeW4First61328, treeW4Second61328] }

def targetW4Formula61328 (x : Cube61328 4) : ℝ :=
  (signValue61328 (x 2) - signValue61328 (x 1)) / 2 -
    (signValue61328 (x 0) * signValue61328 (x 1) +
      signValue61328 (x 0) * signValue61328 (x 2) +
      signValue61328 (x 3) * signValue61328 (x 1) +
      signValue61328 (x 3) * signValue61328 (x 2)) / 4

def coordinateQueryMass61328 {n m : ℕ}
    (law : Law61328 n m) (coordinate : Fin n) : ℝ :=
  ∑ j, law.weight j *
    uniformAverage61328 (fun x =>
      if coordinate ∈ queriedCoordinates61328 (law.tree j) x
      then 1 else 0)

def maximumCoordinateQueryMass61328 {n m : ℕ}
    (law : Law61328 n m) : ℝ :=
  sSup (Set.range (coordinateQueryMass61328 law))

def witnessW4_61328 : Prop :=
  probabilityLaw61328 lawW4_61328 ∧
    legalLaw61328 lawW4_61328 2 ∧
    treeDepth61328 treeW4First61328 = 2 ∧
    treeDepth61328 treeW4Second61328 = 2 ∧
    expectedQueryOptimal61328 treeW4First61328 ∧
    expectedQueryOptimal61328 treeW4Second61328 ∧
    (∀ x, mixtureTarget61328 lawW4_61328 x =
      targetW4Formula61328 x) ∧
    variance61328 (mixtureTarget61328 lawW4_61328) = 3 / 4 ∧
    (∀ coordinate : Fin 4,
      coordinateQueryMass61328 lawW4_61328 coordinate = 1 / 2) ∧
    maximumCoordinateQueryMass61328 lawW4_61328 = 1 / 2 ∧
    variance61328 (mixtureTarget61328 lawW4_61328) =
      (3 / 2 : ℝ) * maximumCoordinateQueryMass61328 lawW4_61328 ∧
    (3 / 2 : ℝ) > 1671 / 1496 ∧
    intrinsicArea61328 4 (mixtureTarget61328 lawW4_61328) =
      13 / 8 ∧
    intrinsicArea61328 4 (mixtureTarget61328 lawW4_61328) < 2

def forcedConstraintsFromSupersolution61328 : Prop :=
  ∀ phi : ℝ → ℝ,
    normalizedPhi61328 phi ∧
      depthTwoLevelMassSupersolution61328 phi →
    forcedPhiConstraints61328 phi

def claim61328 : Prop :=
  noSeparableLevelMassReserve61328 ∧
    forcedConstraintsFromSupersolution61328 ∧
    literalChainCertificate61328 ∧
    singleLiteralCertificate61328 ∧
    exactForcedEndpointBounds61328 ∧
    witnessW1_61328 ∧
    varianceAndObstructionW1_61328 ∧
    witnessW2_61328 ∧
    witnessW4_61328

end

end MathlibPlus.Open.ResearchFormalization.Claim61328
