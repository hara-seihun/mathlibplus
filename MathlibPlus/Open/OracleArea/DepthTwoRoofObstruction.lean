import Mathlib

noncomputable section

namespace MathlibPlus.Open.OracleArea

abbrev Spin := Bool
abbrev Cube (n : ℕ) := Fin n → Spin
abbrev BooleanFunction (n : ℕ) := Cube n → Spin
abbrev Target (n : ℕ) := Cube n → ℝ

/-- The numerical value of the two signs, with `false` representing `-1`. -/
def spinValue (b : Spin) : ℝ := if b then 1 else -1

def targetOfBoolean {n : ℕ} (f : BooleanFunction n) : Target n :=
  fun x => spinValue (f x)

inductive DecisionTree (n : ℕ) where
  | leaf (value : Spin) : DecisionTree n
  | node (coordinate : Fin n) (negative positive : DecisionTree n) : DecisionTree n

def DecisionTree.evaluate {n : ℕ} : DecisionTree n → Cube n → Spin
  | .leaf value, _ => value
  | .node coordinate negative positive, x =>
      if x coordinate then positive.evaluate x else negative.evaluate x

def DecisionTree.depth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _ => 0
  | .node _ negative positive =>
      max negative.depth positive.depth + 1

def DecisionTree.represents {n : ℕ} (tree : DecisionTree n)
    (f : BooleanFunction n) : Prop :=
  ∀ x : Cube n, tree.evaluate x = f x

/-- Deterministic decision-tree depth, as the minimum depth of a representing tree. -/
def decisionDepth {n : ℕ} (f : BooleanFunction n) : ℕ :=
  sInf {d : ℕ | ∃ tree : DecisionTree n, tree.depth = d ∧ tree.represents f}

def lpFeasible {n : ℕ} (u : Target n)
    (weight : BooleanFunction n → ℝ) : Prop :=
  (∀ f, 0 ≤ weight f) ∧
    (∑ f : BooleanFunction n, weight f = 1) ∧
      (∀ x : Cube n,
        (∑ f : BooleanFunction n, weight f * spinValue (f x)) = u x) ∧
        (∀ f, decisionDepth f > 2 → weight f = 0)

def lpObjective {n : ℕ} (weight : BooleanFunction n → ℝ) : ℝ :=
  ∑ f : BooleanFunction n, weight f * (decisionDepth f : ℝ)

/-- The finite LP appearing in the depth-weighted atomic convex roof. -/
def depthTwoRoof {n : ℕ} (u : Target n) : ℝ :=
  sInf {cost : ℝ | ∃ weight, lpFeasible u weight ∧ lpObjective weight = cost}

def diagonalSdpFeasible {n : ℕ} (u : Target n)
    (matrix : BooleanFunction n → BooleanFunction n → ℝ) : Prop :=
  (∀ f g, f ≠ g → matrix f g = 0) ∧
    (∀ f, 0 ≤ matrix f f) ∧
      (∑ f : BooleanFunction n, matrix f f = 1) ∧
        (∀ x : Cube n,
          (∑ f : BooleanFunction n, matrix f f * spinValue (f x)) = u x) ∧
          (∀ f, decisionDepth f > 2 → matrix f f = 0)

def diagonalSdpObjective {n : ℕ}
    (matrix : BooleanFunction n → BooleanFunction n → ℝ) : ℝ :=
  ∑ f : BooleanFunction n, matrix f f * (decisionDepth f : ℝ)

/-- The same finite program written as a diagonal positive-semidefinite program. -/
def diagonalSdpRoof {n : ℕ} (u : Target n) : ℝ :=
  sInf {cost : ℝ |
    ∃ matrix, diagonalSdpFeasible u matrix ∧ diagonalSdpObjective matrix = cost}

def finiteRoofIsDiagonalSdp : Prop :=
  ∀ (n : ℕ) (u : Target n),
    (∃ weight, lpFeasible u weight) →
      (∃ weight, lpFeasible u weight ∧ lpObjective weight = depthTwoRoof u) ∧
        depthTwoRoof u = diagonalSdpRoof u ∧
          (∃ matrix,
            diagonalSdpFeasible u matrix ∧ diagonalSdpObjective matrix = diagonalSdpRoof u)

def cube2Lex (j : Fin 4) : Cube 2 :=
  fun i =>
    if i = 0 then decide (j.val ≥ 2) else decide (j.val % 2 = 1)

def cube3Lex (j : Fin 8) : Cube 3 :=
  fun i =>
    match i.val with
    | 0 => decide (j.val ≥ 4)
    | 1 => decide (j.val / 2 % 2 = 1)
    | _ => decide (j.val % 2 = 1)

def table2 {α : Type} (values : Fin 4 → α) : Cube 2 → α :=
  fun x =>
    if x 0 then
      if x 1 then values 3 else values 2
    else if x 1 then values 1 else values 0

def booleanTable2 (values : Fin 4 → Spin) : BooleanFunction 2 :=
  fun x =>
    if x 0 then
      if x 1 then values 3 else values 2
    else if x 1 then values 1 else values 0

def f3 : BooleanFunction 3 := fun x => x 0

def h3 : BooleanFunction 3 := fun x => if x 2 then x 1 else x 0

def f3Target : Target 3 := targetOfBoolean f3
def h3Target : Target 3 := targetOfBoolean h3
def g3 : Target 3 := fun x => (f3Target x + h3Target x) / 2

def g3Table : Fin 8 → ℝ :=
  ![(-1 : ℝ), -1, -1, 0, 1, 0, 1, 1]

def g3HasDisplayedTable : Prop :=
  ∀ j : Fin 8, g3 (cube3Lex j) = g3Table j

def pairWeight {n : ℕ} (p q : BooleanFunction n) : BooleanFunction n → ℝ :=
  fun f => if f = p then 1 / 2 else if f = q then 1 / 2 else 0

def pairMixture {n : ℕ} (p q : BooleanFunction n) : Target n :=
  fun x => (spinValue (p x) + spinValue (q x)) / 2

def singleWeight {n : ℕ} (p : BooleanFunction n) : BooleanFunction n → ℝ :=
  fun f => if f = p then 1 else 0

def globalL (u : Target 3) : ℝ :=
  -u ![false, false, false] +
    (1 / 2) * u ![false, true, true] +
      (1 / 2) * u ![true, false, false]

def constant3 (b : Spin) : BooleanFunction 3 := fun _ => b

def dictator3 (j : Fin 3) : BooleanFunction 3 := fun x => x j

def signedDictator3 (j : Fin 3) : BooleanFunction 3 :=
  fun x => Bool.not (x j)

def depthOneCensus : Prop :=
  ∀ f : BooleanFunction 3,
    decisionDepth f = 1 →
      (∃ j : Fin 3, f = dictator3 j ∨ f = signedDictator3 j)

def globalDualCertificate : Prop :=
  depthOneCensus ∧
    (∀ b : Spin, globalL (targetOfBoolean (constant3 b)) = 0) ∧
      (∀ j : Fin 3,
        globalL (targetOfBoolean (dictator3 j)) = 1 ∧
          globalL (targetOfBoolean (signedDictator3 j)) = -1) ∧
        (∀ f : BooleanFunction 3,
          decisionDepth f ≤ 2 →
            globalL (targetOfBoolean f) ≤ (decisionDepth f : ℝ)) ∧
          (∀ f : BooleanFunction 3, globalL (targetOfBoolean f) ≤ 2)

def upperCertificateForG : Prop :=
  lpFeasible g3 (pairWeight f3 h3) ∧
    lpObjective (pairWeight f3 h3) = 3 / 2 ∧
      pairMixture f3 h3 = g3

def restrict3 (u : Target 3) (coordinate : Fin 3) (branch : Spin) : Target 2 :=
  fun z =>
    if coordinate = 0 then u ![branch, z 0, z 1]
    else if coordinate = 1 then u ![z 0, branch, z 1]
    else u ![z 0, z 1, branch]

def g1m : Target 2 := restrict3 g3 0 false
def g1p : Target 2 := restrict3 g3 0 true
def g2m : Target 2 := restrict3 g3 1 false
def g2p : Target 2 := restrict3 g3 1 true
def g3m : Target 2 := restrict3 g3 2 false
def g3p : Target 2 := restrict3 g3 2 true

def u1m : Target 2 := table2 ![(-1 : ℝ), -1, -1, 0]
def u1p : Target 2 := table2 ![(1 : ℝ), 0, 1, 1]
def u2m : Target 2 := table2 ![(-1 : ℝ), -1, 1, 0]
def u2p : Target 2 := table2 ![(-1 : ℝ), 0, 1, 1]
def u3m : Target 2 := table2 ![(-1 : ℝ), -1, 1, 1]
def u3p : Target 2 := table2 ![(-1 : ℝ), 0, 0, 1]

def dual2 (coefficient target : Target 2) : ℝ :=
  ∑ x : Cube 2, coefficient x * target x

def constant2 (b : Spin) : BooleanFunction 2 := fun _ => b

def dictator2 (j : Fin 2) : BooleanFunction 2 := fun x => x j

def signedDictator2 (j : Fin 2) : BooleanFunction 2 :=
  fun x => Bool.not (x j)

def dualCertificate2 (coefficient : Target 2) : Prop :=
  (∑ x : Cube 2, coefficient x = 0) ∧
    (∀ b : Spin, dual2 coefficient (targetOfBoolean (constant2 b)) = 0) ∧
      (∀ j : Fin 2,
        dual2 coefficient (targetOfBoolean (dictator2 j)) ≤ 1 ∧
          dual2 coefficient (targetOfBoolean (signedDictator2 j)) ≤ 1) ∧
        (∀ f : BooleanFunction 2, dual2 coefficient (targetOfBoolean f) ≤ 2) ∧
          (∀ f : BooleanFunction 2,
            decisionDepth f ≤ 2 →
              dual2 coefficient (targetOfBoolean f) ≤ (decisionDepth f : ℝ))

def y1m : Target 2 := table2 ![(0 : ℝ), -1 / 2, -1 / 2, 1]
def y1p : Target 2 := table2 ![(1 / 2 : ℝ), -1, 0, 1 / 2]
def y2m : Target 2 := table2 ![(-1 / 2 : ℝ), 0, 1, -1 / 2]
def y2p : Target 2 := table2 ![(-1 : ℝ), 1 / 2, 1 / 2, 0]
def y3m : Target 2 := table2 ![(-1 / 2 : ℝ), 0, 1 / 2, 0]
def y3p : Target 2 := table2 ![(-1 / 2 : ℝ), 0, 0, 1 / 2]

def a0000 : BooleanFunction 2 := booleanTable2 ![false, false, false, false]
def a0001 : BooleanFunction 2 := booleanTable2 ![false, false, false, true]
def a1111 : BooleanFunction 2 := booleanTable2 ![true, true, true, true]
def a1011 : BooleanFunction 2 := booleanTable2 ![true, false, true, true]
def a0010 : BooleanFunction 2 := booleanTable2 ![false, false, true, false]
def a0011 : BooleanFunction 2 := booleanTable2 ![false, false, true, true]
def a0111 : BooleanFunction 2 := booleanTable2 ![false, true, true, true]
def a0101 : BooleanFunction 2 := booleanTable2 ![false, true, false, true]

def twoAtomDecomposition (u : Target 2) (p q : BooleanFunction 2)
    (depthP depthQ : ℕ) : Prop :=
  pairMixture p q = u ∧
    decisionDepth p = depthP ∧
      decisionDepth q = depthQ ∧
        lpFeasible u (pairWeight p q) ∧
          lpObjective (pairWeight p q) =
            ((depthP : ℝ) + depthQ) / 2

def oneAtomDecomposition (u : Target 2) (p : BooleanFunction 2)
    (depthP : ℕ) : Prop :=
  targetOfBoolean p = u ∧
    decisionDepth p = depthP ∧
      lpFeasible u (singleWeight p) ∧
        lpObjective (singleWeight p) = depthP

def sixRestrictionCertificates : Prop :=
  (g1m = u1m ∧ g1p = u1p ∧ g2m = u2m ∧ g2p = u2p ∧ g3m = u3m ∧ g3p = u3p) ∧
    (depthTwoRoof u1m = 1 ∧ depthTwoRoof u1p = 1 ∧
      depthTwoRoof u2m = 3 / 2 ∧ depthTwoRoof u2p = 3 / 2 ∧
        depthTwoRoof u3m = 1 ∧ depthTwoRoof u3p = 1) ∧
      (dualCertificate2 y1m ∧ dual2 y1m u1m = 1 ∧
          twoAtomDecomposition u1m a0000 a0001 0 2) ∧
        (dualCertificate2 y1p ∧ dual2 y1p u1p = 1 ∧
          twoAtomDecomposition u1p a1111 a1011 0 2) ∧
          (dualCertificate2 y2m ∧ dual2 y2m u2m = 3 / 2 ∧
            twoAtomDecomposition u2m a0010 a0011 2 1) ∧
            (dualCertificate2 y2p ∧ dual2 y2p u2p = 3 / 2 ∧
              twoAtomDecomposition u2p a0011 a0111 1 2) ∧
              (dualCertificate2 y3m ∧ dual2 y3m u3m = 1 ∧
                oneAtomDecomposition u3m a0011 1) ∧
                (dualCertificate2 y3p ∧ dual2 y3p u3p = 1 ∧
                  twoAtomDecomposition u3p a0011 a0101 1 1)

def expectation {n : ℕ} (u : Target n) : ℝ :=
  (1 / (Fintype.card (Cube n) : ℝ)) * ∑ x : Cube n, u x

def variance {n : ℕ} (u : Target n) : ℝ :=
  expectation (fun x => (u x - expectation u) ^ 2)

def restrict2 (u : Target 2) (coordinate : Fin 2) (branch : Spin) : Target 1 :=
  fun z => if coordinate = 0 then u ![branch, z 0] else u ![z 0, branch]

def restrict1 (u : Target 1) (branch : Spin) : Target 0 :=
  fun _ => u ![branch]

def area0 (u : Target 0) : ℝ := variance u

def area1 (u : Target 1) : ℝ :=
  variance u +
    ((area0 (restrict1 u false) + area0 (restrict1 u true)) / 2)

def area2 (u : Target 2) : ℝ :=
  variance u +
    min
      ((area1 (restrict2 u 0 false) + area1 (restrict2 u 0 true)) / 2)
      ((area1 (restrict2 u 1 false) + area1 (restrict2 u 1 true)) / 2)

def area3 (u : Target 3) : ℝ :=
  variance u +
    min
      ((area2 (restrict3 u 0 false) + area2 (restrict3 u 0 true)) / 2)
      (min
        ((area2 (restrict3 u 1 false) + area2 (restrict3 u 1 true)) / 2)
        ((area2 (restrict3 u 2 false) + area2 (restrict3 u 2 true)) / 2))

def firstRevealArea (u : Target 3) (coordinate : Fin 3) : ℝ :=
  variance u +
    if coordinate = 0 then
      (area2 (restrict3 u 0 false) + area2 (restrict3 u 0 true)) / 2
    else if coordinate = 1 then
      (area2 (restrict3 u 1 false) + area2 (restrict3 u 1 true)) / 2
    else
      (area2 (restrict3 u 2 false) + area2 (restrict3 u 2 true)) / 2

def exactDepthTwoRoofObstruction : Prop :=
  decisionDepth f3 = 1 ∧
    decisionDepth h3 = 2 ∧
      g3HasDisplayedTable ∧
        finiteRoofIsDiagonalSdp ∧
          upperCertificateForG ∧
            globalDualCertificate ∧
              depthOneCensus ∧
                globalL g3 = 3 / 2 ∧
                depthTwoRoof g3 = 3 / 2 ∧
                  sixRestrictionCertificates ∧
                    expectation g3 = 0 ∧
                      variance g3 = 3 / 4 ∧
                        (variance g3 +
                            min
                              ((depthTwoRoof g1m + depthTwoRoof g1p) / 2)
                              (min
                                ((depthTwoRoof g2m + depthTwoRoof g2p) / 2)
                                ((depthTwoRoof g3m + depthTwoRoof g3p) / 2))) >
                          depthTwoRoof g3 ∧
                          area3 g3 = 17 / 16 ∧
                            area3 g3 < 2 ∧
                              firstRevealArea g3 0 = 17 / 16 ∧
                                firstRevealArea g3 1 = 25 / 16 ∧
                                  firstRevealArea g3 2 = 13 / 8

end MathlibPlus.Open.OracleArea
