import MathlibPlus.Open.Research.R4031Claim51988

namespace MathlibPlus.Open.ResearchFormalization.OracleClaim61183

open scoped BigOperators
open MathlibPlus.Open.Research.R4031Claim51988

noncomputable section

abbrev RationalTable (n : ℕ) := Cube n → ℝ
abbrev BooleanFunction (n : ℕ) := Atom n
abbrev BooleanLaw (n : ℕ) := BooleanFunction n → ℝ

def rowIndex {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i : Fin n, if x i then 2 ^ i.1 else 0

def maskAtom {n : ℕ} (m : ℕ) : BooleanFunction n :=
  fun x => Nat.testBit m (rowIndex x)

def rationalValue (b : Bool) : ℝ :=
  if b then 1 else -1

def booleanValue {n : ℕ} (a : BooleanFunction n) : RationalTable n :=
  fun x => rationalValue (a x)

noncomputable def mean {n : ℕ} (u : RationalTable n) : ℝ :=
  (∑ x : Cube n, u x) / (Fintype.card (Cube n) : ℝ)

noncomputable def variance {n : ℕ} (u : RationalTable n) : ℝ :=
  mean (fun x => (u x - mean u) ^ 2)

noncomputable def treeDepth {n : ℕ} : QueryTree n → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max (treeDepth negative) (treeDepth positive)

noncomputable def minimumWorstDepth {n : ℕ}
    (a : BooleanFunction n) : ℕ :=
  sInf {d : ℕ |
    ∃ tree : QueryTree n,
      tree.noRepeat ∧ tree.determines a ∧ treeDepth tree ≤ d}

noncomputable def componentCost {n : ℕ} (a : BooleanFunction n) : ℝ :=
  (minimumWorstDepth a : ℝ) * variance (booleanValue a)

def lawIsProbability {n : ℕ} (law : BooleanLaw n) : Prop :=
  (∀ a, 0 ≤ law a) ∧
    (∑ a : BooleanFunction n, law a) = 1

noncomputable def lawExpectedCost {n : ℕ} (law : BooleanLaw n) : ℝ :=
  ∑ a : BooleanFunction n, law a * componentCost a

def lawRepresents {n : ℕ} (law : BooleanLaw n)
    (u : RationalTable n) : Prop :=
  lawIsProbability law ∧
    ∀ x, ∑ a : BooleanFunction n, law a * booleanValue a x = u x

noncomputable def convexRoof {n : ℕ} (u : RationalTable n) : ℝ :=
  sInf {z : ℝ |
    ∃ law : BooleanLaw n, lawRepresents law u ∧ z = lawExpectedCost law}

def lawDepthBounded {n : ℕ} (law : BooleanLaw n) (k : ℕ) : Prop :=
  ∀ a, law a ≠ 0 → minimumWorstDepth a ≤ k

noncomputable def diracLaw {n : ℕ} (a : BooleanFunction n) : BooleanLaw n :=
  let _ : DecidableEq (BooleanFunction n) := Classical.decEq _
  fun b => if b = a then 1 else 0

noncomputable def twoAtomLaw {n : ℕ}
    (a b : BooleanFunction n) (weight : ℝ) : BooleanLaw n :=
  let _ : DecidableEq (BooleanFunction n) := Classical.decEq _
  fun c => if c = a then weight else if c = b then 1 - weight else 0

def orderedCube {n : ℕ} (r : Fin (2 ^ n)) : Cube n :=
  fun i => Nat.testBit r.1 i.1

noncomputable def affineValue {n : ℕ}
    (coefficients : Fin (2 ^ n) → ℝ) (u : RationalTable n) : ℝ :=
  ∑ r : Fin (2 ^ n), coefficients r * u (orderedCube r)

def h : BooleanFunction 3 := maskAtom 71
def ell : BooleanFunction 3 := maskAtom 15

def g : RationalTable 3 :=
  fun x => (6 / 7 : ℝ) * booleanValue h x +
    (1 / 7 : ℝ) * booleanValue ell x

def gLaw : BooleanLaw 3 :=
  twoAtomLaw h ell (6 / 7 : ℝ)

def childEmbedding (i : Fin 3) (s : Bool) (x : Cube 2) : Cube 3 :=
  match i.1 with
  | 0 => ![s, x 0, x 1]
  | 1 => ![x 0, s, x 1]
  | _ => ![x 0, x 1, s]

def childTable (u : RationalTable 3) (i : Fin 3) (s : Bool) :
    RationalTable 2 :=
  fun x => u (childEmbedding i s x)

noncomputable def childRoof (i : Fin 3) (s : Bool) : ℝ :=
  convexRoof (childTable g i s)

noncomputable def childAverageRoof (i : Fin 3) : ℝ :=
  (childRoof i false + childRoof i true) / 2

noncomputable def childPrimal (i : Fin 3) (s : Bool) : BooleanLaw 2 :=
  match i.1, s with
  | 0, false =>
      twoAtomLaw (maskAtom 3) (maskAtom 11) (1 / 7 : ℝ)
  | 0, true =>
      twoAtomLaw (maskAtom 1) (maskAtom 3) (6 / 7 : ℝ)
  | 1, false => diracLaw (maskAtom 3)
  | 1, true =>
      twoAtomLaw (maskAtom 3) (maskAtom 5) (1 / 7 : ℝ)
  | _, false =>
      twoAtomLaw (maskAtom 7) (maskAtom 15) (6 / 7 : ℝ)
  | _, true =>
      twoAtomLaw (maskAtom 0) (maskAtom 4) (1 / 7 : ℝ)

noncomputable def childPrimalValue (i : Fin 3) (s : Bool) : ℝ :=
  match i.1, s with
  | 0, false => 10 / 7
  | 0, true => 10 / 7
  | 1, false => 1
  | 1, true => 1
  | _, false => 9 / 7
  | _, true => 9 / 7

def childCertificate (i : Fin 3) (s : Bool) : Fin 4 → ℝ :=
  match i.1, s with
  | 0, false => ![1 / 2, 0, -3 / 4, 1 / 4]
  | 0, true => ![3 / 4, -1 / 4, -1 / 4, -1 / 4]
  | 1, _ => ![1 / 2, 0, 0, -1 / 2]
  | _, false => ![1 / 4, 1 / 4, 1 / 4, -3 / 4]
  | _, true => ![-1 / 4, 0, 3 / 4, -1 / 2]

noncomputable def childCertificateValue (i : Fin 3) (s : Bool) : ℝ :=
  affineValue (childCertificate i s) (childTable g i s)

def depthVarianceCertificate : Fin 8 → ℝ :=
  ![3 / 32, 21 / 32, 0, -1 / 4, -21 / 32, -3 / 32, 1 / 4, 0]

noncomputable def depthVarianceAffine (u : RationalTable 3) : ℝ :=
  affineValue depthVarianceCertificate u

noncomputable def bellmanArea : ℝ :=
  sInf {z : ℝ |
    ∃ policy : QueryTree 3,
      policy.complete ∧
        z = policyLoss policy (fun x => (g x : ℝ))}

/-- The component-depth roof has the sharp cap, but its three-cube witness has
exact roof value `13/7`, child values `(10/7,1,9/7)`, and Bellman defect
`1/49`; all Boolean tables and the listed primal/dual certificates remain on
the concrete finite cubes. -/
def claim61183 : Prop :=
  (∀ (n : ℕ) (u : RationalTable n) (law : BooleanLaw n) (k : ℕ),
    lawRepresents law u →
      lawDepthBounded law k →
        convexRoof u ≤ lawExpectedCost law ∧
          lawExpectedCost law ≤ k) ∧
  (minimumWorstDepth h = 2 ∧ minimumWorstDepth ell = 1) ∧
  (mean (booleanValue h) = 0 ∧ mean (booleanValue ell) = 0) ∧
  variance g = 43 / 49 ∧
  lawRepresents gLaw g ∧
  lawExpectedCost gLaw = 13 / 7 ∧
  convexRoof g = 13 / 7 ∧
  depthVarianceAffine g = 13 / 7 ∧
  (∀ a : BooleanFunction 3,
    depthVarianceAffine (booleanValue a) ≤ componentCost a) ∧
  (∀ i : Fin 3, 0 < variance g + childAverageRoof i - convexRoof g) ∧
  childRoof 0 false = 10 / 7 ∧
  childRoof 0 true = 10 / 7 ∧
  childRoof 1 false = 1 ∧
  childRoof 1 true = 1 ∧
  childRoof 2 false = 9 / 7 ∧
  childRoof 2 true = 9 / 7 ∧
  (∀ i : Fin 3, ∀ s : Bool,
    lawRepresents (childPrimal i s) (childTable g i s) ∧
      lawExpectedCost (childPrimal i s) = childPrimalValue i s ∧
      childCertificateValue i s = childPrimalValue i s ∧
      (∀ a : BooleanFunction 2,
        affineValue (childCertificate i s) (booleanValue a) ≤
          componentCost a)) ∧
  (variance g + min (childAverageRoof 0)
      (min (childAverageRoof 1) (childAverageRoof 2)) - convexRoof g =
    1 / 49) ∧
  bellmanArea = 173 / 98 ∧
  bellmanArea < 2

end
end MathlibPlus.Open.ResearchFormalization.OracleClaim61183
