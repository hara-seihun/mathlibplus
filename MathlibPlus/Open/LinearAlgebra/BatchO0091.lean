import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.LinearAlgebra

abbrev Qubit := Fin 2
abbrev TwoQubit := Qubit × Qubit
abbrev QMatrix := Matrix Qubit Qubit ℂ
abbrev TwoQubitMatrix := Matrix TwoQubit TwoQubit ℂ
abbrev JointIndex := Fin 4
abbrev JointMatrix := Matrix JointIndex JointIndex ℂ

/-- The Pauli matrices used by the two-qubit operators in the admitted claims. -/
def pauliI : QMatrix :=
  fun i j => if i = j then 1 else 0

def pauliX : QMatrix :=
  fun i j =>
    if i = 0 ∧ j = 1 then 1
    else if i = 1 ∧ j = 0 then 1
    else 0

def pauliY : QMatrix :=
  fun i j =>
    if i = 0 ∧ j = 1 then -Complex.I
    else if i = 1 ∧ j = 0 then Complex.I
    else 0

def pauliZ : QMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 1 ∧ j = 1 then -1
    else 0

def tensorMatrix (A B : QMatrix) : TwoQubitMatrix :=
  fun i j => A i.1 j.1 * B i.2 j.2

def qmul (A B : QMatrix) : QMatrix :=
  fun i j => ∑ k : Qubit, A i k * B k j

def twoQubitMul (A B : TwoQubitMatrix) : TwoQubitMatrix :=
  fun i j => ∑ k : TwoQubit, A i k * B k j

def jointMatrixMul (A B : JointMatrix) : JointMatrix :=
  fun i j => ∑ k : JointIndex, A i k * B k j

def rowVec (M : QMatrix) : TwoQubit → ℂ :=
  fun ij => M ij.1 ij.2

def tensorAction (A B : QMatrix) (v : TwoQubit → ℂ) : TwoQubit → ℂ :=
  fun ij => ∑ p : Qubit, ∑ q : Qubit, A ij.1 p * B ij.2 q * v (p, q)

def jointPair (i : JointIndex) : TwoQubit :=
  match i.1 with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | _ => (1, 1)

def jointSign (i : JointIndex) : ℂ :=
  if (jointPair i).1 = 0 then 1 else -1

def jointS : JointMatrix :=
  fun i j => if i = j then jointSign i else 0

def jointT : JointMatrix :=
  fun i j =>
    if i = j then
      if (jointPair i).2 = 0 then 1 else -1
    else 0

def jointST : JointMatrix := jointMatrixMul jointS jointT

def heatChannel (lam : ℝ) (A : JointMatrix) : JointMatrix :=
  ((1 + (lam : ℂ)) / 4) •
      (A + jointMatrixMul jointST (jointMatrixMul A jointST)) +
    ((1 - (lam : ℂ)) / 4) •
      (jointMatrixMul jointS (jointMatrixMul A jointS) +
        jointMatrixMul jointT (jointMatrixMul A jointT))

def heatSchurMatrix (lam : ℝ) : JointMatrix :=
  ![![1, 0, 0, (lam : ℂ)],
    ![0, 1, (lam : ℂ), 0],
    ![0, (lam : ℂ), 1, 0],
    ![(lam : ℂ), 0, 0, 1]]

def schurMultiply (M A : JointMatrix) : JointMatrix :=
  fun i j => M i j * A i j

def matrixUnit (i j : JointIndex) : JointMatrix :=
  fun a b => if a = i ∧ b = j then 1 else 0

def oneFlip (i j : JointIndex) : Prop :=
  let p := jointPair i
  let q := jointPair j
  (p.1 ≠ q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ p.2 ≠ q.2)

def oppositeCorner (i j : JointIndex) : Prop :=
  let p := jointPair i
  let q := jointPair j
  p.1 ≠ q.1 ∧ p.2 ≠ q.2

/-- Exact Schur matrix of the heat channel in the ordered joint-X basis
`(++,+-,-+,--)`, including its action on the three coherence classes. -/
def claim13488 : Prop :=
  ∀ lam : ℝ,
    (∀ A : JointMatrix, heatChannel lam A = schurMultiply (heatSchurMatrix lam) A) ∧
    (∀ i : JointIndex, heatChannel lam (matrixUnit i i) = matrixUnit i i) ∧
    (∀ i j : JointIndex, oneFlip i j → heatChannel lam (matrixUnit i j) = 0) ∧
    (∀ i j : JointIndex, oppositeCorner i j →
      heatChannel lam (matrixUnit i j) = (lam : ℂ) • matrixUnit i j)

def qubitDephasing (lam : ℝ) (A : QMatrix) : QMatrix :=
  ((1 + (lam : ℂ)) / 2) • A +
    ((1 - (lam : ℂ)) / 2) • qmul pauliX (qmul A pauliX)

def encodeRelativeQubit (A : QMatrix) : JointMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then A 0 0
    else if i = 0 ∧ j = 3 then A 0 1
    else if i = 3 ∧ j = 0 then A 1 0
    else if i = 3 ∧ j = 3 then A 1 1
    else 0

def binaryLog (x : ℝ) : ℝ := Real.log x / Real.log 2

def binaryEntropy (p : ℝ) : ℝ :=
  -(p * binaryLog p + (1 - p) * binaryLog (1 - p))

def encodedCoherentInformation (lam : ℝ) : ℝ :=
  1 - binaryEntropy ((1 - lam) / 2)

def negativity (lam : ℝ) : ℝ := |lam| / 2

def logarithmicNegativity (lam : ℝ) : ℝ := binaryLog (1 + |lam|)

def lambdaQ (q : ℕ) : ℝ := Real.rpow 2 (-(q : ℝ) / 2)

def inverseAmplification (q : ℕ) : ℝ := Real.rpow 2 ((q : ℝ) / 2)

def universalGramPositive (lam : ℝ) : Prop := lam ^ 2 ≤ (1 : ℝ) / 3

/-- The dyadic safe region, its two sharp optimizations, and the exact
`lam=1/2` information and negativity values. -/
def claim13495 : Prop :=
  (∀ lam : ℝ, ∀ A : QMatrix,
    heatChannel lam (encodeRelativeQubit A) =
      encodeRelativeQubit (qubitDephasing lam A)) ∧
  (∀ q : ℕ, universalGramPositive (lambdaQ q) ↔ 2 ≤ q) ∧
  (∀ q : ℕ, 2 ≤ q →
    encodedCoherentInformation (lambdaQ q) ≤ encodedCoherentInformation (lambdaQ 2) ∧
      (encodedCoherentInformation (lambdaQ q) = encodedCoherentInformation (lambdaQ 2) ↔ q = 2)) ∧
  (∀ q : ℕ, 2 ≤ q →
    inverseAmplification 2 ≤ inverseAmplification q ∧
      (inverseAmplification q = inverseAmplification 2 ↔ q = 2)) ∧
  (negativity (1 / 2) = 1 / 4) ∧
  (logarithmicNegativity (1 / 2) = binaryLog (3 / 2)) ∧
  (encodedCoherentInformation (1 / 2) = (3 / 4) * binaryLog 3 - 1) ∧
  (0 < (3 / 4) * binaryLog 3 - 1)

def isHermitian (A : TwoQubitMatrix) : Prop :=
  ∀ i j, A i j = star (A j i)

def isPSD (A : TwoQubitMatrix) : Prop :=
  ∀ v : TwoQubit → ℂ,
    0 ≤ (∑ i : TwoQubit, ∑ j : TwoQubit, star (v i) * A i j * v j).re

def compactPartialTranspose (A : TwoQubitMatrix) : TwoQubitMatrix :=
  fun i j => A (i.1, j.2) (j.1, i.2)

def isCompactPPT (A : TwoQubitMatrix) : Prop :=
  isPSD (compactPartialTranspose A)

def nullGauge (k : Fin 7) : TwoQubitMatrix :=
  if k = 0 then tensorMatrix pauliY pauliI
  else if k = 1 then tensorMatrix pauliY pauliX
  else if k = 2 then tensorMatrix pauliY pauliY
  else if k = 3 then tensorMatrix pauliY pauliZ
  else if k = 4 then tensorMatrix pauliI pauliZ
  else if k = 5 then tensorMatrix pauliX pauliZ
  else tensorMatrix pauliZ pauliZ

def nullPerturbation (c : Fin 7 → ℝ) : TwoQubitMatrix :=
  ∑ k : Fin 7, (c k : ℂ) • nullGauge k

def visibleGram (x g : ℝ) : TwoQubitMatrix :=
  ((2 + (x : ℂ)) / 4) • tensorMatrix pauliI pauliI -
    (1 / 2 : ℂ) • tensorMatrix pauliX pauliX -
    ((g : ℂ) / 4) • tensorMatrix pauliZ pauliY

def fullKernelCompletionExists (x g : ℝ) : Prop :=
  ∃ c : Fin 7 → ℝ,
    let Q := visibleGram x g + nullPerturbation c
    isHermitian Q ∧ isPSD Q ∧ isCompactPPT Q

/-- The sharp full seven-gauge PSD and compact-PPT completion threshold. -/
def claim13499 : Prop :=
  ∀ x g : ℝ, 0 ≤ x → x ≤ 1 →
    (fullKernelCompletionExists x g ↔ |g| ≤ x)

def simultaneousConjugation (M : QMatrix) : QMatrix :=
  qmul (qmul pauliX M) pauliX

/-- Weyl actions under row-vectorization and the two simultaneous-conjugation
 eigenspaces. -/
def claim13504 : Prop :=
  (∀ M : QMatrix,
    tensorAction pauliX pauliI (rowVec M) = rowVec (qmul pauliX M)) ∧
  (∀ M : QMatrix,
    tensorAction pauliI pauliX (rowVec M) = rowVec (qmul M pauliX)) ∧
  (∀ M : QMatrix,
    tensorAction pauliX pauliX (rowVec M) =
      rowVec (qmul (qmul pauliX M) pauliX)) ∧
  (∀ M : QMatrix,
    simultaneousConjugation M = M ↔
      ∃ a b : ℂ, M = a • pauliI + b • pauliX) ∧
  (∀ M : QMatrix,
    simultaneousConjugation M = -M ↔
      ∃ a b : ℂ, M = a • pauliZ + b • (Complex.I • pauliY))

end MathlibPlus.Open.LinearAlgebra
