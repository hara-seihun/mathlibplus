import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev Cube (n : Nat) := Fin n → Bool
abbrev Q3MaskTuple := Fin 3 → Fin 16
abbrev Q3Raw := Fin 3 → Cube 3 → Bool
abbrev Q4Raw := Fin 4 → Cube 4 → Bool
abbrev Unary := Fin 2 → Bool
abbrev SquareCountTriple := (Nat × Nat) × ((Nat × Nat) × (Nat × Nat))
abbrev EdgeState := (Bool × Bool) × (Bool × Bool)

def bit4 (m k : Nat) : Bool :=
  decide (m / (2 ^ k) % 2 = 1)

def tableIndex (a b : Bool) : Nat :=
  if a then if b then 3 else 1 else if b then 2 else 0

def maskValue (m : Nat) (a b : Bool) : Bool :=
  bit4 m (tableIndex a b)

def maskOnes (m : Fin 16) : Nat :=
  (if maskValue m.val false false then 1 else 0) +
    (if maskValue m.val true false then 1 else 0) +
    (if maskValue m.val false true then 1 else 0) +
    (if maskValue m.val true true then 1 else 0)

def q3Point (x₀ x₁ x₂ : Bool) : Cube 3 :=
  fun i => if i = 0 then x₀ else if i = 1 then x₁ else x₂

def q3PointOn (i j : Fin 3) (iValue jValue thirdValue : Bool) : Cube 3 :=
  fun k => if k = i then iValue else if k = j then jValue else thirdValue

def q3Input (i : Fin 3) (x : Cube 3) : Bool × Bool :=
  if i = 0 then (x 1, x 2) else if i = 1 then (x 0, x 2) else (x 0, x 1)

def q3Value (g : Q3MaskTuple) (i : Fin 3) (x : Cube 3) : Bool :=
  let input := q3Input i x
  maskValue (g i).val input.1 input.2

def maskTuple (m₀ m₁ m₂ : Fin 16) : Q3MaskTuple :=
  fun i => if i = 0 then m₀ else if i = 1 then m₁ else m₂

def G1 : Q3MaskTuple := maskTuple 6 6 7
def G2 : Q3MaskTuple := maskTuple 6 7 14
def G3 : Q3MaskTuple := maskTuple 6 14 6
def G4 : Q3MaskTuple := maskTuple 15 6 6

def supportTuple (s : Fin 4) : Q3MaskTuple :=
  if s = 0 then G1 else if s = 1 then G2 else if s = 2 then G3 else G4

def specifiedTruthTableMasks : Fin 4 → Fin 16 :=
  fun s => if s = 0 then 6 else if s = 1 then 7 else if s = 2 then 14 else 15

def q3MaskTupleValid (g : Q3MaskTuple) : Prop :=
  ∀ i x y, (∀ k, k ≠ i → x k = y k) → q3Value g i x = q3Value g i y

def selectedCount (b : Bool) : Nat := if b then 1 else 0

def q3SquareCount (g : Q3MaskTuple) (i j k : Fin 3) (fixed : Bool) : Nat :=
  selectedCount (q3Value g i (q3PointOn i j false false fixed)) +
    selectedCount (q3Value g i (q3PointOn i j false true fixed)) +
    selectedCount (q3Value g j (q3PointOn j i false false fixed)) +
    selectedCount (q3Value g j (q3PointOn j i false true fixed))

def q3SquareCounts (g : Q3MaskTuple) : SquareCountTriple :=
  ((q3SquareCount g 0 1 2 false, q3SquareCount g 0 1 2 true),
    ((q3SquareCount g 0 2 1 false, q3SquareCount g 0 2 1 true),
      (q3SquareCount g 1 2 0 false, q3SquareCount g 1 2 0 true)))

def q3C4Free (g : Q3MaskTuple) : Prop :=
  q3SquareCount g 0 1 2 false < 4 ∧
    q3SquareCount g 0 1 2 true < 4 ∧
    q3SquareCount g 0 2 1 false < 4 ∧
    q3SquareCount g 0 2 1 true < 4 ∧
    q3SquareCount g 1 2 0 false < 4 ∧
    q3SquareCount g 1 2 0 true < 4

/-- The four masks, tuples, square counts, and literal C4-freeness in claim 40592. -/
def fourDeterministicC4FreeQ3EdgeTuples40592 : Prop :=
  specifiedTruthTableMasks 0 = 6 ∧
    specifiedTruthTableMasks 1 = 7 ∧
    specifiedTruthTableMasks 2 = 14 ∧
    specifiedTruthTableMasks 3 = 15 ∧
    supportTuple 0 = G1 ∧
    supportTuple 1 = G2 ∧
    supportTuple 2 = G3 ∧
    supportTuple 3 = G4 ∧
    q3SquareCounts G1 = ((2, 2), ((3, 2), (3, 2))) ∧
    q3SquareCounts G2 = ((3, 2), ((2, 3), (3, 3))) ∧
    q3SquareCounts G3 = ((2, 3), ((2, 2), (2, 3))) ∧
    q3SquareCounts G4 = ((3, 3), ((3, 3), (2, 2))) ∧
    (∀ s : Fin 4, q3MaskTupleValid (supportTuple s)) ∧
    q3C4Free G1 ∧ q3C4Free G2 ∧ q3C4Free G3 ∧ q3C4Free G4

def directionDensity (i : Fin 3) : ℚ :=
  ((∑ s : Fin 4, maskOnes ((supportTuple s) i)) : ℚ) / 16

def transitionCount (i j : Fin 3) (upward : Bool) : Nat :=
  ∑ s : Fin 4, ∑ third : Bool,
    let g := supportTuple s
    let low := q3Value g i (q3PointOn i j false false third)
    let high := q3Value g i (q3PointOn i j false true third)
    if upward then
      if low = false ∧ high = true then 1 else 0
    else if low = true ∧ high = false then 1 else 0

def upwardTransitionProbability (i j : Fin 3) : ℚ :=
  (transitionCount i j true : ℚ) / 8

def downwardTransitionProbability (i j : Fin 3) : ℚ :=
  (transitionCount i j false : ℚ) / 8

def minorityOrientationDefect (i j : Fin 3) : ℚ :=
  min (upwardTransitionProbability i j) (downwardTransitionProbability i j)

/-- The uniform-mixture density and ordered transition statistics in claim 40593. -/
def uniformTripleMixtureStatistics40593 : Prop :=
  (∀ i : Fin 3, directionDensity i = (5 : ℚ) / 8) ∧
    (∀ i j : Fin 3, i ≠ j →
      upwardTransitionProbability i j = (3 : ℚ) / 8 ∧
        downwardTransitionProbability i j = (3 : ℚ) / 8 ∧
          minorityOrientationDefect i j = (3 : ℚ) / 8)

def q3SquareState (g : Q3MaskTuple) (i j k : Fin 3) (fixed : Bool) : EdgeState :=
  ((q3Value g i (q3PointOn i j false false fixed),
      q3Value g i (q3PointOn i j false true fixed)),
    (q3Value g j (q3PointOn j i false false fixed),
      q3Value g j (q3PointOn j i false true fixed)))

def pairStateMultiplicity (i j k : Fin 3) (state : EdgeState) : Nat :=
  ∑ s : Fin 4, ∑ fixed : Bool,
    if q3SquareState (supportTuple s) i j k fixed = state then 1 else 0

def st00 : Bool × Bool := (false, false)
def st01 : Bool × Bool := (false, true)
def st10 : Bool × Bool := (true, false)
def st11 : Bool × Bool := (true, true)

def pairSquareMarginalIs40594 (i j k : Fin 3) : Prop :=
  pairStateMultiplicity i j k (st01, st01) = 2 ∧
    pairStateMultiplicity i j k (st10, st10) = 2 ∧
    pairStateMultiplicity i j k (st01, st11) = 1 ∧
    pairStateMultiplicity i j k (st10, st11) = 1 ∧
    pairStateMultiplicity i j k (st11, st01) = 1 ∧
    pairStateMultiplicity i j k (st11, st10) = 1

def oneDirectionMarginalCount (i j k : Fin 3) (state : Bool × Bool) : Nat :=
  ∑ s : Fin 4, ∑ fixed : Bool,
    if (q3SquareState (supportTuple s) i j k fixed).1 = state then 1 else 0

def oneDirectionMarginalBCount (i j k : Fin 3) (state : Bool × Bool) : Nat :=
  ∑ s : Fin 4, ∑ fixed : Bool,
    if (q3SquareState (supportTuple s) i j k fixed).2 = state then 1 else 0

/-- The square-state atoms and one-direction marginal in claim 40594. -/
def completePairSquareStateMarginal40594 : Prop :=
  pairSquareMarginalIs40594 0 1 2 ∧
    pairSquareMarginalIs40594 0 2 1 ∧
    pairSquareMarginalIs40594 1 2 0 ∧
    (∀ (i j k : Fin 3),
      (i = 0 ∧ j = 1 ∧ k = 2) ∨
        (i = 0 ∧ j = 2 ∧ k = 1) ∨
          (i = 1 ∧ j = 2 ∧ k = 0) →
      oneDirectionMarginalCount i j k st00 = 0 ∧
        oneDirectionMarginalCount i j k st01 = 3 ∧
          oneDirectionMarginalCount i j k st10 = 3 ∧
            oneDirectionMarginalCount i j k st11 = 2 ∧
              oneDirectionMarginalBCount i j k st00 = 0 ∧
                oneDirectionMarginalBCount i j k st01 = 3 ∧
                  oneDirectionMarginalBCount i j k st10 = 3 ∧
                    oneDirectionMarginalBCount i j k st11 = 2)

def q3RawOfMasks (g : Q3MaskTuple) : Q3Raw :=
  fun i x => q3Value g i x

def permutedCube (σ : Equiv.Perm (Fin 3)) (x : Cube 3) : Cube 3 :=
  fun i => x (σ i)

def permuteQ3Raw (σ : Equiv.Perm (Fin 3)) (g : Q3Raw) : Q3Raw :=
  fun i x => g (σ.symm i) (permutedCube σ x)

def q3Orbit : Set Q3Raw :=
  {g | ∃ σ : Equiv.Perm (Fin 3), ∃ s : Fin 4,
    g = permuteQ3Raw σ (q3RawOfMasks (supportTuple s))}

def tUnary : Unary := fun b => if b = 0 then false else true
def barTUnary : Unary := fun b => !tUnary b
def oneUnary : Unary := fun _ => true

def q3Boundary (g : Q3Raw) (fixedCoordinate : Fin 3) (side : Bool) : Unary × Unary :=
  if fixedCoordinate = 0 then
    ((fun y => g 1 (q3Point side false y)),
      (fun y => g 2 (q3Point side y false)))
  else if fixedCoordinate = 1 then
    ((fun y => g 0 (q3Point false side y)),
      (fun y => g 2 (q3Point y side false)))
  else
    ((fun y => g 0 (q3Point false y side)),
      (fun y => g 1 (q3Point y false side)))

def q3OrbitBoundary (fixedCoordinate : Fin 3) (side : Bool) : Set (Unary × Unary) :=
  {signature | ∃ g ∈ q3Orbit, signature = q3Boundary g fixedCoordinate side}

def B0 : Set (Unary × Unary) :=
  {(tUnary, tUnary), (tUnary, oneUnary), (oneUnary, tUnary)}

def B1 : Set (Unary × Unary) :=
  {(barTUnary, barTUnary), (barTUnary, oneUnary), (oneUnary, barTUnary)}

/-- The orbit size and the disjoint zero/one boundary signatures in claim 40597. -/
def fourthOrderBoundarySignatures40597 : Prop :=
  Set.ncard q3Orbit = 15 ∧
    (∀ fixedCoordinate : Fin 3,
      q3OrbitBoundary fixedCoordinate false = B0 ∧
        q3OrbitBoundary fixedCoordinate true = B1) ∧
      Disjoint B0 B1

def q4Point (x₀ x₁ x₂ x₃ : Bool) : Cube 4 :=
  fun i =>
    if i = 0 then x₀ else if i = 1 then x₁ else if i = 2 then x₂ else x₃

def q4FacePoint (fixedCoordinate : Fin 4) (side : Bool) (y : Cube 3) : Cube 4 :=
  if fixedCoordinate = 0 then q4Point side (y 0) (y 1) (y 2)
  else if fixedCoordinate = 1 then q4Point (y 0) side (y 1) (y 2)
  else if fixedCoordinate = 2 then q4Point (y 0) (y 1) side (y 2)
  else q4Point (y 0) (y 1) (y 2) side

def q4FaceCoordinate (fixedCoordinate : Fin 4) (localCoordinate : Fin 3) : Fin 4 :=
  if fixedCoordinate = 0 then
    if localCoordinate = 0 then 1 else if localCoordinate = 1 then 2 else 3
  else if fixedCoordinate = 1 then
    if localCoordinate = 0 then 0 else if localCoordinate = 1 then 2 else 3
  else if fixedCoordinate = 2 then
    if localCoordinate = 0 then 0 else if localCoordinate = 1 then 1 else 3
  else
    if localCoordinate = 0 then 0 else if localCoordinate = 1 then 1 else 2

def q4Face (g : Q4Raw) (fixedCoordinate : Fin 4) (side : Bool) : Q3Raw :=
  fun localCoordinate y =>
    g (q4FaceCoordinate fixedCoordinate localCoordinate)
      (q4FacePoint fixedCoordinate side y)

def q4EdgeTupleValid (g : Q4Raw) : Prop :=
  ∀ i x y, (∀ k, k ≠ i → x k = y k) → g i x = g i y

def q4FacesInParticularOrbit (g : Q4Raw) : Prop :=
  ∀ fixedCoordinate : Fin 4, ∀ side : Bool,
    q4Face g fixedCoordinate side ∈ q3Orbit

def sharedQ2SignatureFromX0Zero (g : Q4Raw) : Unary × Unary :=
  q3Boundary (q4Face g 0 false) 0 true

def sharedQ2SignatureFromX1One (g : Q4Raw) : Unary × Unary :=
  q3Boundary (q4Face g 1 true) 0 false

/-- The incompatible x₀=0 and x₁=1 face restrictions in claim 40598. -/
def noQ4ExtensionOfParticularTripleLaw40598 : Prop :=
  (¬ ∃ g : Q4Raw, q4EdgeTupleValid g ∧ q4FacesInParticularOrbit g) ∧
    (∀ g : Q4Raw, q4EdgeTupleValid g → q4FacesInParticularOrbit g →
      sharedQ2SignatureFromX0Zero g = sharedQ2SignatureFromX1One g ∧
        sharedQ2SignatureFromX0Zero g ∈ B1 ∧
          sharedQ2SignatureFromX1One g ∈ B0 ∧
            Disjoint B0 B1)

end MathlibPlus.Open.ResearchFormalization
