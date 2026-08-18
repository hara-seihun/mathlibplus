import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaFixedQueryLevelRankDepthRoofObstructionClaim61245

noncomputable section

abbrev Spin := Bool
abbrev Cube (n : ℕ) := Fin n → Spin
abbrev BooleanFunction (n : ℕ) := Cube n → Spin
abbrev RealTable (n : ℕ) := Cube n → ℝ

/-- `false` is the sign `-1`, as in the little-endian tables in the claim. -/
def spinValue : Spin → ℝ
  | false => -1
  | true => 1

def rowIndex {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i : Fin n, if x i then 2 ^ i.val else 0

def rowIndexFin {n : ℕ} (x : Cube n) : Fin (2 ^ n) :=
  Fin.ofNat (2 ^ n) (rowIndex x)

def rowTable {n : ℕ} {α : Type} (values : Fin (2 ^ n) → α) : Cube n → α :=
  fun x => values (rowIndexFin x)

def maskTable (n mask : ℕ) : BooleanFunction n :=
  fun x => Nat.testBit mask (rowIndex x)

def realBooleanTable {n : ℕ} (h : BooleanFunction n) : RealTable n :=
  fun x => spinValue (h x)

inductive DecisionTree (n : ℕ) where
  | leaf (value : Spin) : DecisionTree n
  | node (coordinate : Fin n) (negative positive : DecisionTree n) : DecisionTree n

def DecisionTree.evaluate {n : ℕ} : DecisionTree n → Cube n → Spin
  | .leaf value, _ => value
  | .node coordinate negative positive, x =>
      if x coordinate then positive.evaluate x else negative.evaluate x

def DecisionTree.depth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _ => 0
  | .node _ negative positive => max negative.depth positive.depth + 1

def DecisionTree.represents {n : ℕ} (tree : DecisionTree n)
    (h : BooleanFunction n) : Prop :=
  ∀ x : Cube n, tree.evaluate x = h x

def legalFrom {n : ℕ} (levels : Fin n → ℕ) (seen : Finset (Fin n))
    (last : Option ℕ) : DecisionTree n → Prop
  | .leaf _ => True
  | .node coordinate negative positive =>
      coordinate ∉ seen ∧
        (match last with
        | none => True
        | some previous => previous < levels coordinate) ∧
        legalFrom levels (insert coordinate seen) (some (levels coordinate)) negative ∧
          legalFrom levels (insert coordinate seen) (some (levels coordinate)) positive

def legalTree {n : ℕ} (levels : Fin n → ℕ) (tree : DecisionTree n) : Prop :=
  legalFrom levels ∅ none tree

/-- Boolean atoms not represented by a fresh-query tree with strictly increasing
levels are excluded from the convex roof. -/
def rankCompatible {n : ℕ} (levels : Fin n → ℕ)
    (h : BooleanFunction n) : Prop :=
  ∃ tree : DecisionTree n, legalTree levels tree ∧ tree.represents h

def rankDepth {n : ℕ} (levels : Fin n → ℕ)
    (h : BooleanFunction n) : ℕ :=
  sInf {d : ℕ |
    ∃ tree : DecisionTree n,
      legalTree levels tree ∧ tree.represents h ∧ tree.depth = d}

def convexRoof {n : ℕ} (levels : Fin n → ℕ) (f : RealTable n) : ℝ :=
  sInf {cost : ℝ |
    ∃ weight : BooleanFunction n → ℝ,
      (∀ h, 0 ≤ weight h) ∧
        (∑ h : BooleanFunction n, weight h = 1) ∧
          (∀ x : Cube n,
            (∑ h : BooleanFunction n, weight h * spinValue (h x)) = f x) ∧
            (∀ h, ¬ rankCompatible levels h → weight h = 0) ∧
              (∑ h : BooleanFunction n,
                weight h * Real.sqrt (rankDepth levels h : ℝ) = cost)}

def globalLevels : Fin 4 → ℕ := ![1, 1, 2, 2]

def L : RealTable 4 := realBooleanTable (maskTable 4 3855)
def H : RealTable 4 := realBooleanTable (maskTable 4 24330)
def g : RealTable 4 := fun x => (1 / 10 : ℝ) * L x + (9 / 10 : ℝ) * H x

def displayedL : Fin 16 → ℝ :=
  ![(1 : ℝ), 1, 1, 1, -1, -1, -1, -1,
    1, 1, 1, 1, -1, -1, -1, -1]

def displayedH : Fin 16 → ℝ :=
  ![(-1 : ℝ), 1, -1, 1, -1, -1, -1, -1,
    1, 1, 1, 1, 1, -1, 1, -1]

def displayedG : Fin 16 → ℝ :=
  ![(-4 : ℝ) / 5, 1, (-4 : ℝ) / 5, 1, -1, -1, -1, -1,
    1, 1, 1, 1, (4 : ℝ) / 5, -1, (4 : ℝ) / 5, -1]

def displayedTables : Prop :=
  (∀ x : Cube 4, L x = rowTable displayedL x) ∧
    (∀ x : Cube 4, H x = rowTable displayedH x) ∧
      (∀ x : Cube 4, g x = rowTable displayedG x)

def coordinateRademacher (i : Fin 4) : RealTable 4 :=
  fun x => spinValue (x i)

def selectorTable : RealTable 4 :=
  fun x => if x 0 = false then coordinateRademacher 3 x
    else -coordinateRademacher 2 x

def selectorIdentity : Prop := ∀ x : Cube 4, H x = selectorTable x

def rootLDepth : Prop := rankDepth globalLevels (maskTable 4 3855) = 1
def rootHDepth : Prop := rankDepth globalLevels (maskTable 4 24330) = 2

def rootRoof : ℝ := convexRoof globalLevels g
def U : ℝ := (1 : ℝ) / 10 + (9 : ℝ) / 10 * Real.sqrt 2

def expectation {n : ℕ} (f : RealTable n) : ℝ :=
  (1 / (Fintype.card (Cube n) : ℝ)) * ∑ x : Cube n, f x

def variance {n : ℕ} (f : RealTable n) : ℝ :=
  expectation (fun x => (f x - expectation f) ^ 2)

def rootNumericalFacts : Prop :=
  variance g = (91 : ℝ) / 100 ∧
    rootRoof ≤ U ∧
      U ^ 2 = (163 : ℝ) / 100 + (9 : ℝ) / 50 * Real.sqrt 2 ∧
        rootRoof ^ 2 ≤ U ^ 2

def insert4 (coordinate : Fin 4) (branch : Spin) (z : Cube 3) : Cube 4 :=
  if coordinate = 0 then ![branch, z 0, z 1, z 2]
  else if coordinate = 1 then ![z 0, branch, z 1, z 2]
  else if coordinate = 2 then ![z 0, z 1, branch, z 2]
  else ![z 0, z 1, z 2, branch]

def restrict4 (f : RealTable 4) (coordinate : Fin 4) (branch : Spin) : RealTable 3 :=
  fun z => f (insert4 coordinate branch z)

def childLevels (coordinate : Fin 4) : Fin 3 → ℕ :=
  if coordinate.val < 2 then ![1, 2, 2] else ![1, 1, 2]

def childRoof (coordinate : Fin 4) (branch : Spin) : ℝ :=
  convexRoof (childLevels coordinate) (restrict4 g coordinate branch)

def childRoofValues : Prop :=
  childRoof 0 false = 1 ∧ childRoof 0 true = 1 ∧
    childRoof 1 false = U ∧ childRoof 1 true = U ∧
      childRoof 2 false = (9 : ℝ) / 10 * Real.sqrt 2 ∧
        childRoof 2 true = (9 : ℝ) / 10 * Real.sqrt 2 ∧
          childRoof 3 false = U ∧ childRoof 3 true = U

def defect (coordinate : Fin 4) : ℝ :=
  variance g +
      (childRoof coordinate false ^ 2 + childRoof coordinate true ^ 2) / 2 -
    U ^ 2

def displayedDefects : Fin 4 → ℝ :=
  ![(7 : ℝ) / 25 - (9 : ℝ) / 50 * Real.sqrt 2,
    (91 : ℝ) / 100,
    (9 : ℝ) / 10 - (9 : ℝ) / 50 * Real.sqrt 2,
    (91 : ℝ) / 100]

def defectValues : Prop := ∀ i : Fin 4, defect i = displayedDefects i

def defectPositivity : Prop := ∀ i : Fin 4, 0 < defect i

def bellmanSupersolutionAt (coordinate : Fin 4) : Prop :=
  rootRoof ^ 2 ≥ variance g +
    (childRoof coordinate false ^ 2 + childRoof coordinate true ^ 2) / 2

def noFirstCoordinate : Prop :=
  ∀ coordinate : Fin 4, ¬ bellmanSupersolutionAt coordinate

def rankA : Fin 3 → ℕ := ![1, 2, 2]
def rankB : Fin 3 → ℕ := ![1, 1, 2]

def eligibleMasks (levels : Fin 3 → ℕ) : Finset (Fin 256) :=
  letI := Classical.propDecidable
  Finset.univ.filter (fun mask => rankCompatible levels (maskTable 3 mask.val))

def eligibleCount (levels : Fin 3 → ℕ) : ℕ :=
  (eligibleMasks levels).card

def certificateEnumerationCount : Prop :=
  eligibleCount rankA = 36 ∧ eligibleCount rankB = 28 ∧
    2 * (36 + 36 + 28 + 28) = 256

def PrimalEntry := ℕ × ℚ

def listSum {α : Type} [AddCommMonoid α] (xs : List α) : α :=
  xs.foldr (· + ·) 0

def primalMass (entries : List PrimalEntry) : ℚ :=
  listSum (entries.map Prod.snd)

def primalBarycenter (n : ℕ) (entries : List PrimalEntry) : RealTable n :=
  fun x => listSum (entries.map (fun entry =>
    (entry.2 : ℝ) * spinValue (maskTable n entry.1 x)))

def primalCost (levels : Fin 3 → ℕ) (entries : List PrimalEntry) : ℝ :=
  listSum (entries.map (fun entry =>
    (entry.2 : ℝ) *
      Real.sqrt (rankDepth levels (maskTable 3 entry.1) : ℝ)))

def dualValue (dual : RealTable 3) (constant : ℝ) (f : RealTable 3) : ℝ :=
  (∑ x : Cube 3, dual x * f x) + constant

def dualFromRows (values : Fin 8 → ℝ) : RealTable 3 := rowTable values

def childRoofCertificate (coordinate : Fin 4) (branch : Spin)
    (levels : Fin 3 → ℕ) (entries : List PrimalEntry)
    (dual : RealTable 3) (dualConstant expected : ℝ) : Prop :=
  convexRoof levels (restrict4 g coordinate branch) = expected ∧
    primalMass entries = 1 ∧
      primalBarycenter 3 entries = restrict4 g coordinate branch ∧
        primalCost levels entries = expected ∧
          dualValue dual dualConstant (restrict4 g coordinate branch) = expected ∧
            (∀ h : BooleanFunction 3, rankCompatible levels h →
              dualValue dual dualConstant (realBooleanTable h) ≤
                Real.sqrt (rankDepth levels h : ℝ))

def entries0m : List PrimalEntry := [(51, 1 / 10), (240, 9 / 10)]
def entries0p : List PrimalEntry := [(51, 1)]
def entries1m : List PrimalEntry := [(51, 1 / 10), (114, 9 / 10)]
def entries1p : List PrimalEntry := [(51, 1 / 10), (114, 9 / 10)]
def entries2m : List PrimalEntry := [(250, 9 / 10), (255, 1 / 10)]
def entries2p : List PrimalEntry := [(0, 1 / 10), (80, 9 / 10)]
def entries3m : List PrimalEntry := [(10, 9 / 10), (15, 1 / 10)]
def entries3p : List PrimalEntry := [(15, 1 / 10), (95, 9 / 10)]

def dual0m : RealTable 3 :=
  dualFromRows ![(0 : ℝ), 0, 0, -1 / 2, 1 / 2, 0, 0, 0]
def dual0p : RealTable 3 :=
  dualFromRows ![(1 : ℝ) / 2, 0, 0, 0, 0, 0, -1 / 2, 0]
def dual1 : RealTable 3 :=
  dualFromRows ![((1 : ℝ) - Real.sqrt 2) / 2, 0, 0, 0,
    Real.sqrt 2 / 2, 0, 0, -1 / 2]
def dual2m : RealTable 3 :=
  dualFromRows ![(-1 : ℝ) / 2, 0,
    (1 - Real.sqrt 2) / 2, (Real.sqrt 2 - 1) / 2,
    0, 0, (1 : ℝ) / 2, 0]
def dual2p : RealTable 3 := dual1
def dual3m : RealTable 3 :=
  dualFromRows ![(0 : ℝ), 0, (1 - Real.sqrt 2) / 2,
    Real.sqrt 2 / 2, 0, -1 / 2, 0, 0]
def dual3p : RealTable 3 :=
  dualFromRows ![(1 : ℝ) - Real.sqrt 2 / 2, 0, 0,
    (Real.sqrt 2 - 1) / 2, (Real.sqrt 2 - 1) / 2,
    -Real.sqrt 2 / 2, 0, 0]

def childRoofCertificates : Prop :=
  childRoofCertificate 0 false rankA entries0m dual0m 0 1 ∧
    childRoofCertificate 0 true rankA entries0p dual0p 0 1 ∧
      childRoofCertificate 1 false rankA entries1m dual1 0 U ∧
        childRoofCertificate 1 true rankA entries1p dual1 0 U ∧
          childRoofCertificate 2 false rankB entries2m dual2m 0
            ((9 : ℝ) / 10 * Real.sqrt 2) ∧
            childRoofCertificate 2 true rankB entries2p dual2p 0
              ((9 : ℝ) / 10 * Real.sqrt 2) ∧
              childRoofCertificate 3 false rankB entries3m dual3m 0 U ∧
                childRoofCertificate 3 true rankB entries3p dual3p 0 U

def insert3 (coordinate : Fin 3) (branch : Spin) (z : Cube 2) : Cube 3 :=
  if coordinate = 0 then ![branch, z 0, z 1]
  else if coordinate = 1 then ![z 0, branch, z 1]
  else ![z 0, z 1, branch]

def insert2 (coordinate : Fin 2) (branch : Spin) (z : Cube 1) : Cube 2 :=
  if coordinate = 0 then ![branch, z 0] else ![z 0, branch]

def insert1 (branch : Spin) (_z : Cube 0) : Cube 1 := ![branch]

def restrict3 (f : RealTable 3) (coordinate : Fin 3) (branch : Spin) : RealTable 2 :=
  fun z => f (insert3 coordinate branch z)

def restrict2 (f : RealTable 2) (coordinate : Fin 2) (branch : Spin) : RealTable 1 :=
  fun z => f (insert2 coordinate branch z)

def restrict1 (f : RealTable 1) (branch : Spin) : RealTable 0 :=
  fun z => f (insert1 branch z)

def area0 (f : RealTable 0) : ℝ := variance f

def area1 (f : RealTable 1) : ℝ :=
  variance f + (area0 (restrict1 f false) + area0 (restrict1 f true)) / 2

def area2 (f : RealTable 2) : ℝ :=
  variance f + min
    ((area1 (restrict2 f 0 false) + area1 (restrict2 f 0 true)) / 2)
    ((area1 (restrict2 f 1 false) + area1 (restrict2 f 1 true)) / 2)

def area3 (f : RealTable 3) : ℝ :=
  variance f + min
    ((area2 (restrict3 f 0 false) + area2 (restrict3 f 0 true)) / 2)
    (min
      ((area2 (restrict3 f 1 false) + area2 (restrict3 f 1 true)) / 2)
      ((area2 (restrict3 f 2 false) + area2 (restrict3 f 2 true)) / 2))

def area4 (f : RealTable 4) : ℝ :=
  variance f + min
    ((area3 (restrict4 f 0 false) + area3 (restrict4 f 0 true)) / 2)
    (min
      ((area3 (restrict4 f 1 false) + area3 (restrict4 f 1 true)) / 2)
      (min
        ((area3 (restrict4 f 2 false) + area3 (restrict4 f 2 true)) / 2)
        ((area3 (restrict4 f 3 false) + area3 (restrict4 f 3 true)) / 2)))

def exactBellmanArea : Prop := area4 g = (73 : ℝ) / 40 ∧ area4 g < 2

def radicalPositivity : Prop :=
  (14 : ℝ) > 9 * Real.sqrt 2 ∧ (5 : ℝ) > Real.sqrt 2

/-- The complete proof-free alignment of admitted claim 61245. -/
def claim61245 : Prop :=
  displayedTables ∧
    selectorIdentity ∧
      rootLDepth ∧ rootHDepth ∧
        rootNumericalFacts ∧
          childRoofValues ∧
            defectValues ∧ defectPositivity ∧ noFirstCoordinate ∧
              childRoofCertificates ∧ certificateEnumerationCount ∧
                exactBellmanArea ∧ radicalPositivity

end
end MathlibPlus.Open.ResearchFormalization.OracleAreaFixedQueryLevelRankDepthRoofObstructionClaim61245
