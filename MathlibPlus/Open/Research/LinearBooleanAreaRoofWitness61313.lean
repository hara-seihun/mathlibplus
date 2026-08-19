import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Research.LinearBooleanAreaRoof61313

abbrev BooleanTable (m : ℕ) := Fin (2 ^ m) → Bool
abbrev RealTable (m : ℕ) := Fin (2 ^ m) → ℝ


def signValue (b : Bool) : ℝ := if b then 1 else -1

def booleanToReal (b : Bool) : ℝ := signValue b

def maskTable (m q : ℕ) : BooleanTable m :=
  fun j => Nat.testBit q j.val

def tableOfBoolean (m : ℕ) (h : BooleanTable m) : RealTable m :=
  fun j => booleanToReal (h j)


def restrictIndex (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (j : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  Fin.ofNat (2 ^ (n + 1))
    ((j.val % 2 ^ i.val) +
      (if b then 2 ^ i.val else 0) +
      2 ^ (i.val + 1) * (j.val / 2 ^ i.val))

def restrictTable (n : ℕ) (u : RealTable (n + 1))
    (i : Fin (n + 1)) (b : Bool) : RealTable n :=
  fun j => u (restrictIndex n i b j)


def uniformAverage (m : ℕ) (u : RealTable m) : ℝ :=
  (((2 ^ m : ℕ) : ℝ)⁻¹) * ∑ j : Fin (2 ^ m), u j

def tableVariance (m : ℕ) (u : RealTable m) : ℝ :=
  let mean := uniformAverage m u
  uniformAverage m (fun j => (u j - mean) ^ 2)

def isConstant {m : ℕ} (u : RealTable m) : Prop :=
  ∀ j : Fin (2 ^ m), u j = u 0

/-- Root-inclusive Bellman area, with a finite-cube infimum representing the minimum. -/
noncomputable def area : (m : ℕ) → RealTable m → ℝ
  | 0, _ => 0
  | n + 1, u =>
      letI : Decidable (isConstant u) := Classical.propDecidable (isConstant u)
      if isConstant u then
        0
      else
        tableVariance (n + 1) u +
          sInf {q : ℝ |
            ∃ i : Fin (n + 1),
              q =
                (area n (restrictTable n u i false) +
                  area n (restrictTable n u i true)) / 2}


def finiteConvexDecomposition (m r : ℕ) (u : RealTable m)
    (weight : Fin r → ℝ) (table : Fin r → BooleanTable m) : Prop :=
  (∀ k : Fin r, 0 ≤ weight k) ∧
    (∑ k : Fin r, weight k = 1) ∧
      (∀ j : Fin (2 ^ m),
        u j = ∑ k : Fin r, weight k * booleanToReal (table k j))

/-- The linear Boolean convex roof of the Bellman area. -/
noncomputable def roof (m : ℕ) (u : RealTable m) : ℝ :=
  sInf {q : ℝ |
    ∃ r : ℕ, ∃ weight : Fin r → ℝ,
      ∃ table : Fin r → BooleanTable m,
        finiteConvexDecomposition m r u weight table ∧
          q = ∑ k : Fin r, weight k * area m (tableOfBoolean m (table k))}

inductive DecisionTree (m : ℕ) where
  | leaf (value : Bool)
  | query (coordinate : Fin m)
      (negativeBranch positiveBranch : DecisionTree m)

def DecisionTree.run {m : ℕ} :
    DecisionTree m → (Fin m → Bool) → Bool
  | DecisionTree.leaf value, _ => value
  | DecisionTree.query coordinate negativeBranch positiveBranch, x =>
      if x coordinate then
        DecisionTree.run positiveBranch x
      else
        DecisionTree.run negativeBranch x

def DecisionTree.depth {m : ℕ} : DecisionTree m → ℕ
  | DecisionTree.leaf _ => 0
  | DecisionTree.query _ negativeBranch positiveBranch =>
      1 + max (DecisionTree.depth negativeBranch)
        (DecisionTree.depth positiveBranch)

def DecisionTree.represents {m : ℕ}
    (tree : DecisionTree m) (h : BooleanTable m) : Prop :=
  ∀ x : Fin m → Bool,
    DecisionTree.run tree x = h (Fin.ofNat (2 ^ m)
      (∑ i : Fin m, if x i then 2 ^ i.val else 0))

noncomputable def minimumDecisionDepth (m : ℕ) (h : BooleanTable m) : ℕ :=
  sInf {d : ℕ |
    ∃ tree : DecisionTree m,
      DecisionTree.depth tree = d ∧ DecisionTree.represents tree h}


def rowSign (j : Fin 4) (i : Fin 2) : ℝ :=
  signValue (Nat.testBit j.val i.val)

def walshTable2 (a b c d : ℝ) : RealTable 2 :=
  fun j =>
    a + b * rowSign j 0 + c * rowSign j 1 +
      d * rowSign j 0 * rowSign j 1

def linearFunctional {m : ℕ} (coefficient u : RealTable m) : ℝ :=
  ∑ j : Fin (2 ^ m), coefficient j * u j


def target61313 : RealTable 3 :=
  ![(1 : ℝ), -1, 1 / 2, -1, 1, 1, -1 / 2, -1]

def atomWeights61313 : Fin 3 → ℝ :=
  ![1 / 4, 1 / 2, 1 / 4]
def atomTables61313 : Fin 3 → BooleanTable 3 :=
  ![maskTable 3 49, maskTable 3 53, maskTable 3 117]

def displayedDecomposition61313 : Prop :=
  (∀ j : Fin 8,
    target61313 j =
      ∑ r : Fin 3,
        atomWeights61313 r * booleanToReal (atomTables61313 r j)) ∧
    (∀ r : Fin 3, 0 ≤ atomWeights61313 r) ∧
      (∑ r : Fin 3, atomWeights61313 r = 1)

def atomData61313 : Prop :=
  area 3 (tableOfBoolean 3 (maskTable 3 49)) = 25 / 16 ∧
    area 3 (tableOfBoolean 3 (maskTable 3 53)) = 2 ∧
      area 3 (tableOfBoolean 3 (maskTable 3 117)) = 25 / 16 ∧
        minimumDecisionDepth 3 (maskTable 3 49) = 3 ∧
          minimumDecisionDepth 3 (maskTable 3 53) = 2 ∧
            minimumDecisionDepth 3 (maskTable 3 117) = 3

def parentCertificate61313 : RealTable 3 :=
  ![(5 : ℝ) / 32, -17 / 32, 7 / 32, -3 / 32,
    11 / 32, 9 / 32, -7 / 32, -5 / 32]

def parentDualCertificate61313 : Prop :=
  (∀ h : BooleanTable 3,
    linearFunctional parentCertificate61313 (tableOfBoolean 3 h) ≤
      area 3 (tableOfBoolean 3 h)) ∧
    linearFunctional parentCertificate61313 target61313 = 57 / 32

def childTable61313 (i : Fin 3) (b : Bool) : RealTable 2 :=
  restrictTable 2 target61313 i b

def childCertificateIndex61313 (i : Fin 3) (b : Bool) : Fin 6 :=
  Fin.ofNat 6 (2 * i.val + if b then 1 else 0)

def childCertificate0_61313 : RealTable 2 :=
  ![(3 : ℝ) / 8, 1 / 8, 1 / 8, -5 / 8]
def childCertificate1_61313 : RealTable 2 :=
  ![-3 / 8, 3 / 8, 5 / 8, -5 / 8]
def childCertificate2_61313 : RealTable 2 :=
  ![5 / 8, -5 / 8, -1 / 8, 1 / 8]
def childCertificate5_61313 : RealTable 2 :=
  ![-1 / 8, 5 / 8, 1 / 8, -5 / 8]

def childCertificates61313 : Fin 6 → RealTable 2 :=
  ![childCertificate0_61313, childCertificate1_61313,
    childCertificate2_61313, childCertificate2_61313,
    childCertificate2_61313, childCertificate5_61313]

def childCertificateValue61313 : Fin 6 → ℝ :=
  ![7 / 8, 5 / 4, 5 / 4, 7 / 8, 17 / 16, 17 / 16]

def childCertificate61313 (i : Fin 3) (b : Bool) : RealTable 2 :=
  childCertificates61313 (childCertificateIndex61313 i b)

def childValue61313 (i : Fin 3) (b : Bool) : ℝ :=
  childCertificateValue61313 (childCertificateIndex61313 i b)

def childDualCertificates61313 : Prop :=
  (∀ i : Fin 3, ∀ b : Bool, ∀ h : BooleanTable 2,
    linearFunctional (childCertificate61313 i b) (tableOfBoolean 2 h) ≤
      area 2 (tableOfBoolean 2 h)) ∧
    (∀ i : Fin 3, ∀ b : Bool,
      linearFunctional (childCertificate61313 i b) (childTable61313 i b) =
        childValue61313 i b)

def childRoofBounds61313 : Prop :=
  ∀ i : Fin 3,
    (roof 2 (childTable61313 i false) +
      roof 2 (childTable61313 i true)) / 2 ≥ 17 / 16

def twoCubeAreaFormula61313 : Prop :=
  ∀ a b c d : ℝ,
    area 2 (walshTable2 a b c d) =
      b ^ 2 + c ^ 2 + 2 * d ^ 2 + min (b ^ 2) (c ^ 2)

def roofBellmanRight61313 (i : Fin 3) : ℝ :=
  tableVariance 3 target61313 +
    (roof 2 (childTable61313 i false) +
      roof 2 (childTable61313 i true)) / 2

def claim61313_exactThreeAtomBellmanWitness : Prop :=
  displayedDecomposition61313 ∧
    atomData61313 ∧
      tableVariance 3 target61313 = 13 / 16 ∧
        roof 3 target61313 ≤ 57 / 32 ∧
          parentDualCertificate61313 ∧
            roof 3 target61313 = 57 / 32 ∧
              area 3 target61313 = 105 / 64 ∧
                area 3 target61313 < roof 3 target61313 ∧
                  roof 3 target61313 < 3 ∧
                    twoCubeAreaFormula61313 ∧
                      childDualCertificates61313 ∧
                        childRoofBounds61313 ∧
                          (∀ i : Fin 3, roofBellmanRight61313 i ≥ 15 / 8) ∧
                            (15 / 8 : ℝ) = roof 3 target61313 + 3 / 32 ∧
                              (∀ i : Fin 3,
                                roofBellmanRight61313 i > roof 3 target61313)

end MathlibPlus.Open.Research.LinearBooleanAreaRoof61313
