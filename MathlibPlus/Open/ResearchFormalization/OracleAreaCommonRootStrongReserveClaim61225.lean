import MathlibPlus.Open.OracleArea.DepthTwoRoofObstruction
import MathlibPlus.Open.Probability.AdmittedBatch49134Area

open scoped BigOperators

noncomputable section

open Classical

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaCommonRootStrongReserveClaim61225

abbrev BooleanCube (n : ℕ) := MathlibPlus.Open.Probability.AdmittedBatch49134.Cube n
abbrev BooleanTable (n : ℕ) := BooleanCube n → Bool
abbrev RealTable (n : ℕ) := BooleanCube n → ℝ

/-- The two signs used by the truth tables, with `false` denoting `-1`. -/
def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

def signedTable {n : ℕ} (a : BooleanTable n) : RealTable n :=
  fun x => signValue (a x)

def isConstantBoolean {n : ℕ} (a : BooleanTable n) : Prop :=
  ∃ b : Bool, ∀ x, a x = b

def isConstantReal {n : ℕ} (u : RealTable n) : Prop :=
  ∃ c : ℝ, ∀ x, u x = c

/-- Removing a queried coordinate preserves the little-endian order of the
remaining coordinates. -/
def restrictBoolean {n : ℕ} (a : BooleanTable (n + 1))
    (i : Fin (n + 1)) (b : Bool) : BooleanTable n :=
  fun x => a (MathlibPlus.Open.Probability.AdmittedBatch49134.insertBit i b x)

def restrictReal {n : ℕ} (u : RealTable (n + 1))
    (i : Fin (n + 1)) (b : Bool) : RealTable n :=
  MathlibPlus.Open.Probability.AdmittedBatch49134.restrictTable u i b

def uniformExpectation {n : ℕ} (u : RealTable n) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : BooleanCube n, u x

def varianceValue {n : ℕ} (u : RealTable n) : ℝ :=
  uniformExpectation (fun x => (u x - uniformExpectation u) ^ 2)

/-- Root-inclusive minimum posterior-variance area. -/
noncomputable def areaValue : (n : ℕ) → RealTable n → ℝ
  | 0, u =>
      if isConstantReal u then 0 else varianceValue u
  | n + 1, u =>
      if isConstantReal u then
        0
      else
        varianceValue u +
          sInf {z : ℝ |
            ∃ i : Fin (n + 1),
              z = (areaValue n (restrictReal u i false) +
                areaValue n (restrictReal u i true)) / 2}

/-- Minimum expected number of fresh coordinate queries for a Boolean table. -/
noncomputable def queryCost : (n : ℕ) → BooleanTable n → ℝ
  | 0, _ => 0
  | n + 1, a =>
      if isConstantBoolean a then
        0
      else
        1 +
          sInf {z : ℝ |
            ∃ i : Fin (n + 1),
              z = (queryCost n (restrictBoolean a i false) +
                queryCost n (restrictBoolean a i true)) / 2}

/-- Exact target area after a minimum-expected-cost prefix computing `a`. -/
noncomputable def constrainedArea :
    (n : ℕ) → BooleanTable n → RealTable n → ℝ
  | 0, _, u => areaValue 0 u
  | n + 1, a, u =>
      if isConstantBoolean a then
        areaValue (n + 1) u
      else
        varianceValue u +
          sInf {z : ℝ |
            ∃ i : Fin (n + 1),
              queryCost (n + 1) a =
                1 +
                  (queryCost n (restrictBoolean a i false) +
                    queryCost n (restrictBoolean a i true)) / 2 ∧
              z =
                (constrainedArea n (restrictBoolean a i false)
                    (restrictReal u i false) +
                  constrainedArea n (restrictBoolean a i true)
                    (restrictReal u i true)) / 2}

def decisionDepthValue {n : ℕ} (a : BooleanTable n) : ℕ :=
  MathlibPlus.Open.OracleArea.decisionDepth a

def rowIndex3 (x : BooleanCube 3) : ℕ :=
  ∑ i : Fin 3, if x i then 2 ^ i.1 else 0

def rowConfiguration3 (r : Fin 8) : BooleanCube 3 :=
  fun i => Nat.testBit r.1 i.1

def maskTable3 (m : ℕ) : BooleanTable 3 :=
  fun x => Nat.testBit m (rowIndex3 x)

def h78 : BooleanTable 3 := maskTable3 78
def ell15 : BooleanTable 3 := maskTable3 15

def displayedH : Fin 8 → ℝ :=
  ![(-1 : ℝ), 1, 1, 1, -1, -1, 1, -1]

def displayedEll : Fin 8 → ℝ :=
  ![(1 : ℝ), 1, 1, 1, -1, -1, -1, -1]

def p : ℝ := 22 / 23
def r : ℝ := 1 / 23

def targetG : RealTable 3 :=
  fun x => p * signedTable h78 x + r * signedTable ell15 x

def displayedG : Fin 8 → ℝ :=
  ![(-21 : ℝ) / 23, 1, 1, 1, -1, -1, (21 : ℝ) / 23, -1]

def targetTableAgreement : Prop :=
  (∀ j : Fin 8, signedTable h78 (rowConfiguration3 j) = displayedH j) ∧
    (∀ j : Fin 8, signedTable ell15 (rowConfiguration3 j) = displayedEll j) ∧
      (∀ j : Fin 8, targetG (rowConfiguration3 j) = displayedG j)

def lawQueryCost : ℝ :=
  p * queryCost 3 h78 + r * queryCost 3 ell15

def childLawQueryCost (i : Fin 3) (b : Bool) : ℝ :=
  p * queryCost 2 (restrictBoolean h78 i b) +
    r * queryCost 2 (restrictBoolean ell15 i b)

def averagedChildQueryCost (i : Fin 3) : ℝ :=
  (∑ b : Bool, childLawQueryCost i b) / 2

def childConstrainedDefect (i : Fin 3) (b : Bool) : ℝ :=
  p *
      (constrainedArea 2 (restrictBoolean h78 i b)
          (restrictReal targetG i b) -
        queryCost 2 (restrictBoolean h78 i b)) +
    r *
      (constrainedArea 2 (restrictBoolean ell15 i b)
          (restrictReal targetG i b) -
        queryCost 2 (restrictBoolean ell15 i b))

def averagedChildConstrainedDefect (i : Fin 3) : ℝ :=
  (∑ b : Bool, childConstrainedDefect i b) / 2

def commonFirstCost (i : Fin 3) : ℝ :=
  varianceValue targetG + averagedChildQueryCost i +
    averagedChildConstrainedDefect i

def commonRootScore (i : Fin 3) : ℝ :=
  lawQueryCost - averagedChildQueryCost i -
    averagedChildConstrainedDefect i

def reserveBudget : ℝ :=
  lawQueryCost - (1 / 2 : ℝ) *
    (1 - uniformExpectation (fun x => (targetG x) ^ 2))

def currentPayment : ℝ :=
  varianceValue targetG + (1 / 2 : ℝ) *
    (1 - uniformExpectation (fun x => (targetG x) ^ 2))

def minimumCommonFirstCost : ℝ :=
  sInf (Set.range commonFirstCost)

def branchAreaH (i : Fin 3) (b : Bool) : ℝ :=
  constrainedArea 2 (restrictBoolean h78 i b) (restrictReal targetG i b)

def branchAreaEll (i : Fin 3) (b : Bool) : ℝ :=
  constrainedArea 2 (restrictBoolean ell15 i b) (restrictReal targetG i b)

def branchFacts : Prop :=
  (∀ b : Bool,
    childLawQueryCost 0 b = 1 ∧
      childConstrainedDefect 0 b =
        (if b then 0 else (-22 : ℝ) / 529) ∧
      (branchAreaH 0 b = if b then 1 else (486 : ℝ) / 529) ∧
      branchAreaEll 0 b = if b then 1 else (969 : ℝ) / 529) ∧
  (∀ b : Bool,
    childLawQueryCost 1 b = 34 / 23 ∧
      childConstrainedDefect 1 b = (-154 : ℝ) / 529 ∧
      branchAreaH 1 b = 628 / 529 ∧
      branchAreaEll 1 b = 628 / 529) ∧
  (∀ b : Bool,
    childLawQueryCost 2 b = 33 / 23 ∧
      childConstrainedDefect 2 b = (-154 : ℝ) / 529 ∧
      branchAreaH 2 b = 605 / 529 ∧
      branchAreaEll 2 b = 605 / 529)

/-- Claim 61225: the exact common-root strong-reserve obstruction for the
specified two-atom Rademacher law. -/
def claim61225 : Prop :=
  targetTableAgreement ∧
    varianceValue targetG = 507 / 529 ∧
    1 - uniformExpectation (fun x => (targetG x) ^ 2) = 22 / 529 ∧
    queryCost 3 h78 = 2 ∧
    queryCost 3 ell15 = 1 ∧
    lawQueryCost = 45 / 23 ∧
    decisionDepthValue h78 = 2 ∧
    decisionDepthValue ell15 = 1 ∧
    branchFacts ∧
    averagedChildQueryCost 0 = 1 ∧
    averagedChildQueryCost 1 = 34 / 23 ∧
    averagedChildQueryCost 2 = 33 / 23 ∧
    averagedChildConstrainedDefect 0 = (-11 : ℝ) / 529 ∧
    averagedChildConstrainedDefect 1 = (-154 : ℝ) / 529 ∧
    averagedChildConstrainedDefect 2 = (-154 : ℝ) / 529 ∧
    commonFirstCost 0 = 1025 / 529 ∧
    commonFirstCost 1 = 1135 / 529 ∧
    commonFirstCost 2 = 1112 / 529 ∧
    reserveBudget = 1024 / 529 ∧
    minimumCommonFirstCost - reserveBudget = 1 / 529 ∧
    (∀ i : Fin 3, commonFirstCost i > reserveBudget) ∧
    commonRootScore 0 = 517 / 529 ∧
    commonRootScore 1 = 407 / 529 ∧
    commonRootScore 2 = 430 / 529 ∧
    currentPayment = 518 / 529 ∧
    areaValue 3 targetG = 2029 / 1058 ∧
    areaValue 3 targetG < 2 ∧
    p * (constrainedArea 3 h78 targetG - queryCost 3 h78) +
        r * (constrainedArea 3 ell15 targetG - queryCost 3 ell15) =
      (-374 : ℝ) / 12167 ∧
    p * (constrainedArea 3 h78 targetG - queryCost 3 h78) +
        r * (constrainedArea 3 ell15 targetG - queryCost 3 ell15) <
      -(1 / 2 : ℝ) *
        (1 - uniformExpectation (fun x => (targetG x) ^ 2))

end MathlibPlus.Open.ResearchFormalization.OracleAreaCommonRootStrongReserveClaim61225

end
