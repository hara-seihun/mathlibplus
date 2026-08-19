import MathlibPlus.Open.ResearchFormalization.RademacherArea
import MathlibPlus.Open.ResearchFormalizationBatch_01a000fa

namespace MathlibPlus.Open.ResearchFormalization.R3691.Claim48064

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalizationBatch_01a000fa

abbrev Cube (n : ℕ) := RademacherCube n

def selectorTreeValue :
    SelectorConstruction.SelectorTree → (ℕ → Bool) → Bool
  | .leaf coordinate, x => x coordinate
  | .branch coordinate left right, x =>
      if x coordinate then selectorTreeValue right x
      else selectorTreeValue left x

/-- The total coordinate embedding needed by the fifteen-coordinate tree; all
coordinates used by selectorTree 3 are read in the Fin 15 carrier. -/
def extendFifteen (x : Fin 15 → Bool) (coordinate : ℕ) : Bool :=
  x (Fin.ofNat 15 coordinate)

def hThreeBoolean (x : Fin 15 → Bool) : Bool :=
  selectorTreeValue (SelectorConstruction.selectorTree 3) (extendFifteen x)

def hThreeValue (x : Cube 15) : ℝ :=
  if hThreeBoolean x then (1 : ℝ) else -1

def booleanValued {n : ℕ} (h : Cube n → ℝ) : Prop :=
  ∀ x : Cube n, h x = 1 ∨ h x = -1

def insertBoolean {n : ℕ} (i : Fin (n + 1)) (b : Bool)
    (x : Cube n) : Cube (n + 1) :=
  Fin.insertNth i b x

def functionConditionalMean {n : ℕ} (h : Cube n → ℝ)
    (cell : Finset (Cube n)) : ℝ :=
  (cell.sum h) / (cell.card : ℝ)

def functionNodeMean {n : ℕ} (h : Cube n → ℝ)
    (tree : DecisionTree n) (path : List Bool) : ℝ :=
  functionConditionalMean h (transcriptCell tree path)

def functionDecisionTreeArea {n : ℕ} (h : Cube n → ℝ)
    (tree : DecisionTree n) : ℝ :=
  tree.internalPaths.sum (fun path =>
    nodeProbability tree path *
      (1 - (functionNodeMean h tree path) ^ 2))

def functionValidDeterminingTree {n : ℕ} (h : Cube n → ℝ)
    (tree : DecisionTree n) : Prop :=
  noRepeat tree ∧ ∀ x : Cube n, tree.evaluate x = h x

noncomputable def functionIntrinsicArea {n : ℕ} (h : Cube n → ℝ) : ℝ :=
  sInf {a : ℝ | ∃ tree : DecisionTree n,
    functionValidDeterminingTree h tree ∧
      a = functionDecisionTreeArea h tree}

def coordinateRestrictionFunction {n : ℕ} (h : Cube (n + 1) → ℝ)
    (i : Fin (n + 1)) (b : Bool) : Cube n → ℝ :=
  fun x => h (insertBoolean i b x)

noncomputable def areaDecrementFunction {n : ℕ}
    (h : Cube (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  functionIntrinsicArea h -
    (functionIntrinsicArea (coordinateRestrictionFunction h i false) +
      functionIntrinsicArea (coordinateRestrictionFunction h i true)) / 2

def hThreeDecrementProfile : Fin 15 → ℝ :=
  ![1, 1 / 2, 1 / 4, 15 / 64, 15 / 64, 1 / 4, 15 / 64, 15 / 64,
    1 / 2, 1 / 4, 15 / 64, 15 / 64, 1 / 4, 15 / 64, 15 / 64]

def walshCharacter {n : ℕ}
    (S : Finset (Fin n)) (x : Cube n) : ℝ :=
  ∏ i ∈ S, rademacherValue (x i)

def walshCoefficient {n : ℕ}
    (h : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  uniformMean (fun x => h x * walshCharacter S x)

def walshSupport {n : ℕ} (h : Cube n → ℝ) : Set (Finset (Fin n)) :=
  {S | walshCoefficient h S ≠ 0}

noncomputable def diagonalFrame {n : ℕ}
    (h : Cube (n + 1) → ℝ) : ℝ :=
  ∑ S : Finset (Fin (n + 1)),
    if S.Nonempty then
      (walshCoefficient h S) ^ 2 /
        ((S.card : ℝ)⁻¹ * ∑ i ∈ S, areaDecrementFunction h i)
    else 0

def universalDiagonalFrameBound : Prop :=
  ∀ (n : ℕ) (h : Cube (n + 1) → ℝ),
    booleanValued h → diagonalFrame h ≤ 2

/-- Claim 48064: the exact recursively selected H₃ frame has the displayed
area/decrement/Walsh data and gives a strict rational counterexample to the
universal diagonal-frame bound. -/
def diagonalFrameFailure_claim48064 : Prop :=
  SelectorConstruction.hThreeUsesFifteenCoordinates ∧
    booleanValued hThreeValue ∧
    (∀ i : Fin 15,
      areaDecrementFunction hThreeValue i = hThreeDecrementProfile i) ∧
    functionIntrinsicArea hThreeValue = 4 ∧
    diagonalFrame hThreeValue =
      969039916512 / 359677883005 ∧
    diagonalFrame hThreeValue =
      2 + 249684150502 / 359677883005 ∧
    (2 : ℝ) < diagonalFrame hThreeValue ∧
    ¬ universalDiagonalFrameBound

end

end MathlibPlus.Open.ResearchFormalization.R3691.Claim48064
