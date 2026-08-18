import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61124

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev History (n : ℕ) := Fin n → Option Bool
abbrev Policy (n : ℕ) := History n → Option (Fin n)
abbrev BooleanTable (n : ℕ) := Cube n → Bool
abbrev RealTable (n : ℕ) := Cube n → ℝ
abbrev BooleanLaw (n : ℕ) := List (BooleanTable n × ℝ)

 def signedBoolean (b : Bool) : ℝ :=
  if b then 1 else -1

def booleanReal {n : ℕ} (h : BooleanTable n) : RealTable n :=
  fun x => signedBoolean (h x)

def compatible {n : ℕ} (h : History n) (x : Cube n) : Prop :=
  ∀ i : Fin n, ∀ b : Bool, h i = some b → x i = b

noncomputable def compatibleOutcomes {n : ℕ} (h : History n) : Finset (Cube n) :=
  letI : DecidableEq (Cube n) := Classical.decEq _
  letI : ∀ x : Cube n, Decidable (compatible h x) :=
    fun x => Classical.propDecidable (compatible h x)
  Finset.univ.filter (fun x => compatible h x)

noncomputable def posteriorMean {n : ℕ} (u : RealTable n) (h : History n) : ℝ :=
  if hs : (compatibleOutcomes h).Nonempty then
    ((compatibleOutcomes h).card : ℝ)⁻¹ *
      (∑ x ∈ compatibleOutcomes h, u x)
  else 0

noncomputable def posteriorVariance {n : ℕ} (u : RealTable n) (h : History n) : ℝ :=
  if hs : (compatibleOutcomes h).Nonempty then
    ((compatibleOutcomes h).card : ℝ)⁻¹ *
      (∑ x ∈ compatibleOutcomes h,
        (u x - posteriorMean u h) ^ 2)
  else 0

def observe {n : ℕ} (h : History n) (x : Cube n) (i : Fin n) : History n :=
  Function.update h i (some (x i))

def historyAt {n : ℕ} (π : Policy n) (x : Cube n) : ℕ → History n
  | 0 => fun _ => none
  | k + 1 =>
      let h := historyAt π x k
      match π h with
      | none => h
      | some i => observe h x i

def legalPolicy {n : ℕ} (π : Policy n) : Prop :=
  ∀ h : History n, ∀ i : Fin n, π h = some i → h i = none

def terminalPolicy {n : ℕ} (u : RealTable n) (π : Policy n) : Prop :=
  ∀ x : Cube n, ∃ k : Fin (n + 1),
    posteriorVariance u (historyAt π x (k : ℕ)) = 0

noncomputable def policyArea {n : ℕ} (u : RealTable n) (π : Policy n) : ℝ :=
  (Fintype.card (Cube n) : ℝ)⁻¹ *
    ∑ k : Fin (n + 1),
      ∑ x : Cube n, posteriorVariance u (historyAt π x (k : ℕ))

noncomputable def bellmanArea (n : ℕ) (u : RealTable n) : ℝ :=
  sInf {r : ℝ |
    ∃ π : Policy n,
      legalPolicy π ∧ terminalPolicy u π ∧ r = policyArea u π}

def tableCost {n : ℕ} (h : BooleanTable n) : ℝ :=
  Real.sqrt (bellmanArea n (booleanReal h))

def lawWeightSum {n : ℕ} (law : BooleanLaw n) : ℝ :=
  (law.map Prod.snd).sum

def lawNonnegative {n : ℕ} (law : BooleanLaw n) : Prop :=
  ∀ entry ∈ law, 0 ≤ entry.2

def validLaw {n : ℕ} (law : BooleanLaw n) : Prop :=
  lawNonnegative law ∧ lawWeightSum law = 1

def lawBarycenter {n : ℕ} (law : BooleanLaw n) : RealTable n :=
  fun x => (law.map (fun entry => entry.2 * booleanReal entry.1 x)).sum

noncomputable def lawCost {n : ℕ} (law : BooleanLaw n) : ℝ :=
  (law.map (fun entry => entry.2 * tableCost entry.1)).sum

noncomputable def convexRoof (n : ℕ) (g : RealTable n) : ℝ :=
  sInf {r : ℝ |
    ∃ law : BooleanLaw n,
      validLaw law ∧ lawBarycenter law = g ∧ r = lawCost law}

def rowNumber (x : Cube 3) : ℕ :=
  Bool.toNat (x 0) + 2 * Bool.toNat (x 1) + 4 * Bool.toNat (x 2)

def tableFromRows (rows : Fin 8 → ℝ) : RealTable 3 :=
  fun x => rows (Fin.ofNat 8 (rowNumber x))

def booleanTableFromMask (m : ℕ) : BooleanTable 3 :=
  fun x => Nat.testBit m (rowNumber x)

def maskTable (m : ℕ) : RealTable 3 :=
  booleanReal (booleanTableFromMask m)

def g : RealTable 3 :=
  tableFromRows
    ![(-1 : ℝ), (-1 : ℝ), 39 / 50, (-1 : ℝ),
      39 / 50, 39 / 50, 39 / 50, -39 / 50]

def restrictTable {n : ℕ} (i : Fin (n + 1)) (b : Bool)
    (u : RealTable (n + 1)) : RealTable n :=
  fun x => u (Fin.succAboveCases i b (fun j => x j))

def uniformMean {n : ℕ} (u : RealTable n) : ℝ :=
  (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ x : Cube n, u x

def tableVariance {n : ℕ} (u : RealTable n) : ℝ :=
  (Fintype.card (Cube n) : ℝ)⁻¹ *
    ∑ x : Cube n, (u x - uniformMean u) ^ 2

def witnessLaw : BooleanLaw 3 :=
  [(booleanTableFromMask 0, 11 / 100),
   (booleanTableFromMask 116, 39 / 50),
   (booleanTableFromMask 244, 11 / 100)]

def affineFunctional (n : ℕ) := ℝ × RealTable n

def affineValue {n : ℕ} (a : affineFunctional n) (u : RealTable n) : ℝ :=
  a.1 + ∑ x : Cube n, a.2 x * u x

def affineMinorant {n : ℕ} (a : affineFunctional n) : Prop :=
  ∀ h : BooleanTable n, affineValue a (booleanReal h) ≤ tableCost h

def roofCertificate {n : ℕ} (u : RealTable n) (v : ℝ) : Prop :=
  ∃ law : BooleanLaw n, ∃ a : affineFunctional n,
    validLaw law ∧ lawBarycenter law = u ∧ lawCost law = v ∧
      affineMinorant a ∧ affineValue a u = v

def childRoofValue (i : Fin 3) (b : Bool) : ℝ :=
  if i = 0 then
    if b then 39 * Real.sqrt 5 / 100 + 11 / 100
    else 89 * Real.sqrt 5 / 200
  else if i = 1 then
    if b then 39 / 50 + 11 * Real.sqrt 5 / 200
    else 89 / 100
  else
    if b then 39 * Real.sqrt 5 / 100
    else 89 * Real.sqrt 5 / 200

def defectValue (i : Fin 3) : ℝ :=
  if i = 0 then
    -429 * Real.sqrt 2 / 2000 + 429 * Real.sqrt 5 / 10000 + 3941 / 10000
  else if i = 1 then
    -429 * Real.sqrt 2 / 2000 + 429 * Real.sqrt 5 / 10000 + 4411 / 20000
  else
    7761 / 20000 - 429 * Real.sqrt 2 / 2000

def upperRoot : ℝ := 39 * Real.sqrt 2 / 50 + 11 / 80

def claim61124 : Prop :=
  lawBarycenter witnessLaw = g ∧
    bellmanArea 3 (maskTable 0) = 0 ∧
    bellmanArea 3 (maskTable 116) = 2 ∧
    bellmanArea 3 (maskTable 244) = 25 / 16 ∧
    convexRoof 3 g ≤ upperRoot ∧
    tableVariance g = 119751 / 160000 ∧
    (∀ i : Fin 3, convexRoof 2 (restrictTable i false g) = childRoofValue i false) ∧
    (∀ i : Fin 3, convexRoof 2 (restrictTable i true g) = childRoofValue i true) ∧
    (∀ i : Fin 3,
      roofCertificate (restrictTable i false g) (childRoofValue i false) ∧
        roofCertificate (restrictTable i true g) (childRoofValue i true)) ∧
    (∀ i : Fin 3,
      tableVariance g +
          (convexRoof 2 (restrictTable i false g) ^ 2 +
            convexRoof 2 (restrictTable i true g) ^ 2) / 2 - upperRoot ^ 2 =
        defectValue i) ∧
    (∀ i : Fin 3,
      0 < tableVariance g +
          (convexRoof 2 (restrictTable i false g) ^ 2 +
            convexRoof 2 (restrictTable i true g) ^ 2) / 2 - upperRoot ^ 2) ∧
    upperRoot ^ 2 ≥ (convexRoof 3 g) ^ 2 ∧
    (∀ i : Fin 3,
      tableVariance g +
          (convexRoof 2 (restrictTable i false g) ^ 2 +
            convexRoof 2 (restrictTable i true g) ^ 2) / 2 > upperRoot ^ 2 ∧
        upperRoot ^ 2 ≥ (convexRoof 3 g) ^ 2)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61124
