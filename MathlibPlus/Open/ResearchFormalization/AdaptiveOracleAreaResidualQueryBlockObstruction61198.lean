import MathlibPlus.Open.DecisionTree.Cost

open scoped BigOperators

open MathlibPlus.Open.DecisionTree.Cost

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaResidualQueryBlockObstruction61198

abbrev SignCube (n : Nat) := Fin n → Sign

abbrev Atom3 := Atom 3

noncomputable def qReal {n : Nat} (h : Atom n) : ℝ :=
  (queryCost n h : ℝ)

noncomputable def restrictQ {n : Nat} (f : SignCube (n + 1) → ℝ)
    (i : Fin (n + 1)) (b : Sign) : SignCube n → ℝ :=
  fun x => f (insertAt i b x)

def constantQ {n : Nat} (f : SignCube n → ℝ) : Prop :=
  ∃ c : ℝ, ∀ x, f x = c

noncomputable def meanQ {n : Nat} (f : SignCube n → ℝ) : ℝ :=
  (∑ x : SignCube n, f x) / (Fintype.card (SignCube n) : ℝ)

noncomputable def varianceQ {n : Nat} (f : SignCube n → ℝ) : ℝ :=
  (∑ x : SignCube n, (f x - meanQ f) ^ 2) /
    (Fintype.card (SignCube n) : ℝ)

def qOptimalRoot {n : Nat} (h : Atom (n + 1)) (i : Fin (n + 1)) : Prop :=
  ¬ IsConstant h ∧
    qReal h =
      1 +
        (qReal (restrict h i .neg) + qReal (restrict h i .pos)) / 2

noncomputable def stoppedCharge :
    (n : Nat) → Atom n → Atom n → Atom n →
      (SignCube n → ℝ) → ℝ
  | 0, driver, h, r, target =>
      (13 / 23 : ℝ) * qReal h +
        (10 / 23 : ℝ) * qReal r
  | n + 1, driver, h, r, target =>
      sInf {c : ℝ |
        (IsConstant driver ∧
            c = (13 / 23 : ℝ) * qReal h +
              (10 / 23 : ℝ) * qReal r) ∨
          (¬ IsConstant driver ∧
            ∃ i : Fin (n + 1),
              qOptimalRoot driver i ∧
                c = varianceQ target +
                  (stoppedCharge n (restrict driver i .neg)
                      (restrict h i .neg) (restrict r i .neg)
                      (restrictQ target i .neg) +
                    stoppedCharge n (restrict driver i .pos)
                      (restrict h i .pos) (restrict r i .pos)
                      (restrictQ target i .pos)) / 2)}

noncomputable def unrestrictedAreaQ :
    (n : Nat) → (SignCube n → ℝ) → ℝ
  | 0, target => 0
  | n + 1, target =>
      sInf {a : ℝ |
        (constantQ target ∧ a = 0) ∨
          (¬ constantQ target ∧
            ∃ i : Fin (n + 1),
              a = varianceQ target +
                (unrestrictedAreaQ n (restrictQ target i .neg) +
                  unrestrictedAreaQ n (restrictQ target i .pos)) / 2)}

def maskAtom (m : Nat) : Atom3 :=
  fun x =>
    if (m / (2 ^ (truthIndex 3 x).val)) % 2 = 1 then
      .pos
    else
      .neg

def h : Atom3 := maskAtom 240

def r : Atom3 := maskAtom 116

noncomputable def hRows : Fin 8 → ℝ :=
  ![(-1 : ℝ), -1, -1, -1, 1, 1, 1, 1]

noncomputable def rRows : Fin 8 → ℝ :=
  ![(-1 : ℝ), -1, 1, -1, 1, 1, 1, -1]

noncomputable def gRows : Fin 8 → ℝ :=
  ![(-1 : ℝ), -1, -3 / 23, -1, 1, 1, 1, 3 / 23]

def hValue : SignCube 3 → ℝ :=
  fun x => (signValue (h x) : ℝ)

def rValue : SignCube 3 → ℝ :=
  fun x => (signValue (r x) : ℝ)

noncomputable def targetG : SignCube 3 → ℝ :=
  fun x => (13 / 23 : ℝ) * hValue x + (10 / 23 : ℝ) * rValue x

def literal3 (i : Fin 3) : Atom3 :=
  fun x => if x i = .pos then .pos else .neg

def literalPositive2 : Atom 2 :=
  fun x => if x 1 = .pos then .pos else .neg

def literalNegativeFirst2 : Atom 2 :=
  fun x => if x 0 = .pos then .neg else .pos

def claim61198_residualQueryCostBlockObstruction : Prop :=
  (∀ x : SignCube 3,
    hValue x = hRows (truthIndex 3 x)) ∧
  (∀ x : SignCube 3,
    rValue x = rRows (truthIndex 3 x)) ∧
  (∀ x : SignCube 3,
    targetG x = gRows (truthIndex 3 x)) ∧
  (h = literal3 2) ∧
  (restrict r 1 .neg = literalPositive2) ∧
  (restrict r 1 .pos = literalNegativeFirst2) ∧
  (restrict h 1 .neg = restrict r 1 .neg) ∧
  (qReal (restrict h 2 .neg) = 0) ∧
  (qReal (restrict h 2 .pos) = 0) ∧
  (qReal (restrict r 2 .neg) + qReal (restrict r 2 .pos)) / 2 = 3 / 2 ∧
  (qReal (restrict r 1 .neg) = 1) ∧
  (qReal (restrict r 1 .pos) = 1) ∧
  (varianceQ (restrictQ targetG 1 .neg) = 1) ∧
  (varianceQ (restrictQ targetG 1 .pos) = 269 / 529) ∧
  (∀ i : Fin 3, qOptimalRoot h i ↔ i = 2) ∧
  (∀ i : Fin 3, qOptimalRoot r i ↔ i = 1) ∧
  qReal h = 1 ∧
  qReal r = 2 ∧
  varianceQ targetG = 399 / 529 ∧
  (13 / 23 : ℝ) * qReal h +
      (10 / 23 : ℝ) * qReal r = 33 / 23 ∧
  stoppedCharge 3 h h r targetG = 744 / 529 ∧
  stoppedCharge 3 r h r targetG = 1895 / 1058 ∧
  (13 / 23 : ℝ) * stoppedCharge 3 h h r targetG +
      (10 / 23 : ℝ) * stoppedCharge 3 r h r targetG =
    19147 / 12167 ∧
  (19147 / 12167 : ℝ) = 33 / 23 + 1690 / 12167 ∧
  (19147 / 12167 : ℝ) > 33 / 23 ∧
  unrestrictedAreaQ 3 targetG = 524 / 529 ∧
  unrestrictedAreaQ 3 targetG < 2

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaResidualQueryBlockObstruction61198
