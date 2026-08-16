import Mathlib

namespace MathlibPlus.Open.OracleAreaSignMatrixLocalPaymentObstruction

noncomputable section

abbrev Sign := Bool

abbrev Coordinate := Fin 4

abbrev SignCube := Coordinate → Sign

def signValue (b : Sign) : ℝ := if b = true then 1 else -1

def coordinateA : Coordinate := 0

def coordinateB : Coordinate := 1

def coordinateC : Coordinate := 2

def coordinateD : Coordinate := 3

def uniformExpectation (X : SignCube → ℝ) : ℝ :=
  (1 / (16 : ℝ)) * Finset.sum Finset.univ X

def uniformVariance (X : SignCube → ℝ) : ℝ :=
  uniformExpectation (fun ω => (X ω - uniformExpectation X) ^ 2)

def rowF (ω : SignCube) : ℝ :=
  if ω coordinateD = false then signValue (ω coordinateA)
  else -signValue (ω coordinateB)

def rowG (ω : SignCube) : ℝ :=
  if ω coordinateC = false then signValue (ω coordinateA)
  else -signValue (ω coordinateB)

def mixtureTarget (ω : SignCube) : ℝ :=
  (rowF ω + rowG ω) / 2

def treeF (ω : SignCube) : List Coordinate :=
  [coordinateD, if ω coordinateD = false then coordinateA else coordinateB]

def treeG (ω : SignCube) : List Coordinate :=
  [coordinateC, if ω coordinateC = false then coordinateA else coordinateB]

def queriesF (i : Coordinate) (ω : SignCube) : Prop :=
  i ∈ treeF ω

def queriesG (i : Coordinate) (ω : SignCube) : Prop :=
  i ∈ treeG ω

noncomputable def indicator (p : Prop) : ℝ :=
  @ite ℝ p (Classical.propDecidable p) 1 0

def mixtureRevealment (i : Coordinate) : ℝ :=
  (1 / 2 : ℝ) *
      uniformExpectation (fun ω => indicator (queriesF i ω)) +
    (1 / 2 : ℝ) *
      uniformExpectation (fun ω => indicator (queriesG i ω))

def selectedCommunication : ℝ :=
  (1 / 2 : ℝ) * uniformExpectation (fun _ : SignCube => (2 : ℝ)) +
    (1 / 2 : ℝ) * uniformExpectation (fun _ : SignCube => (2 : ℝ))

def suppliedCommunication (i : Coordinate) : ℝ :=
  (1 / 2 : ℝ) *
      uniformExpectation (fun ω => (2 : ℝ) - indicator (queriesF i ω)) +
    (1 / 2 : ℝ) *
      uniformExpectation (fun ω => (2 : ℝ) - indicator (queriesG i ω))

def localPolicyOrder (ω : SignCube) : List Coordinate :=
  [coordinateA, coordinateB] ++
    if ω coordinateA = ω coordinateB then [coordinateC, coordinateD] else []

def matchingFiber (revealed : Finset Coordinate) (ω : SignCube) : Finset SignCube :=
  Finset.univ.filter (fun ω' => ∀ i ∈ revealed, ω' i = ω i)

def conditionalExpectation (X : SignCube → ℝ)
    (revealed : Finset Coordinate) (ω : SignCube) : ℝ :=
  (1 / ((matchingFiber revealed ω).card : ℝ)) *
    Finset.sum (matchingFiber revealed ω) (fun ω' => X ω')

def conditionalVariance (X : SignCube → ℝ)
    (revealed : Finset Coordinate) (ω : SignCube) : ℝ :=
  conditionalExpectation
    (fun ω' => (X ω' - conditionalExpectation X revealed ω) ^ 2)
    revealed ω

def afterA : Finset Coordinate := {coordinateA}

def afterAB : Finset Coordinate := insert coordinateB afterA

def afterABC : Finset Coordinate := insert coordinateC afterAB

def localPolicyAreaAt (ω : SignCube) : ℝ :=
  conditionalVariance mixtureTarget (∅ : Finset Coordinate) ω +
    conditionalVariance mixtureTarget afterA ω +
    if ω coordinateA = ω coordinateB then
      conditionalVariance mixtureTarget afterAB ω +
        conditionalVariance mixtureTarget afterABC ω
    else 0

def localPolicyArea : ℝ := uniformExpectation localPolicyAreaAt

def claim60159 : Prop :=
  (∀ ω : SignCube,
    (treeF ω).length = 2 ∧
      (treeG ω).length = 2 ∧
      (treeF ω).Nodup ∧
      (treeG ω).Nodup ∧
      (localPolicyOrder ω).Nodup) ∧
    uniformExpectation mixtureTarget = 0 ∧
    uniformVariance mixtureTarget = (3 / 4 : ℝ) ∧
    mixtureRevealment coordinateA = (1 / 2 : ℝ) ∧
    mixtureRevealment coordinateB = (1 / 2 : ℝ) ∧
    mixtureRevealment coordinateC = (1 / 2 : ℝ) ∧
    mixtureRevealment coordinateD = (1 / 2 : ℝ) ∧
    selectedCommunication = (2 : ℝ) ∧
    (∀ i : Coordinate, suppliedCommunication i = (3 / 2 : ℝ)) ∧
    (∀ i : Coordinate,
      selectedCommunication - suppliedCommunication i = mixtureRevealment i) ∧
    (∀ i : Coordinate,
      ¬(uniformVariance mixtureTarget ≤
        selectedCommunication - suppliedCommunication i)) ∧
    localPolicyArea = (13 / 8 : ℝ) ∧
    (13 / 8 : ℝ) < 2

end

end MathlibPlus.Open.OracleAreaSignMatrixLocalPaymentObstruction
