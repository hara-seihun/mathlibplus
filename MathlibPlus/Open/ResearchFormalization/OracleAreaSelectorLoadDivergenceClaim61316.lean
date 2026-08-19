import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaSelectorLoadDivergenceClaim61316

open scoped BigOperators
open Classical
noncomputable section

abbrev Cube (I : Type*) := I → Bool
abbrev RealFunction (I : Type*) := Cube I → ℝ

def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

def booleanValued {I : Type*} (f : RealFunction I) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

def cubeMean {I : Type*} [Fintype I] (f : RealFunction I) : ℝ :=
  (Fintype.card (Cube I) : ℝ)⁻¹ * ∑ x, f x

def cubeVariance {I : Type*} [Fintype I] (f : RealFunction I) : ℝ :=
  let μ := cubeMean f
  cubeMean (fun x => (f x - μ) ^ 2)

inductive QueryTree (I : Type*) where
  | leaf (value : ℝ)
  | query (coordinate : I) (negative positive : QueryTree I)

def treeDepth {I : Type*} : QueryTree I → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max (treeDepth negative) (treeDepth positive)

def treeRun {I : Type*} : QueryTree I → Cube I → ℝ
  | .leaf value, _ => value
  | .query coordinate negative positive, x =>
      if x coordinate then treeRun positive x else treeRun negative x

def treePaths {I : Type*} : QueryTree I → Finset (List Bool)
  | .leaf _ => {[]}
  | .query _ negative positive =>
      insert []
        ((treePaths negative).image (fun path => false :: path) ∪
          (treePaths positive).image (fun path => true :: path))

def treeQueryAt {I : Type*} : QueryTree I → List Bool → Option I
  | .leaf _, _ => none
  | .query coordinate _ _, [] => some coordinate
  | .query _ negative positive, branch :: path =>
      if branch then treeQueryAt positive path else treeQueryAt negative path

def treeFollows {I : Type*} : QueryTree I → Cube I → List Bool → Prop
  | _, _, [] => True
  | .leaf _, _, _ :: _ => False
  | .query coordinate negative positive, x, branch :: path =>
      if x coordinate = branch then
        if branch then treeFollows positive x path
        else treeFollows negative x path
      else False

noncomputable def treeCell {I : Type*} [Fintype I]
    (tree : QueryTree I) (path : List Bool) : Finset (Cube I) :=
  Finset.univ.filter (fun x => treeFollows tree x path)

def treeProbability {I : Type*} [Fintype I]
    (tree : QueryTree I) (path : List Bool) : ℝ :=
  (treeCell tree path).card / (Fintype.card (Cube I) : ℝ)

def treeConditionalMean {I : Type*} [Fintype I]
    (f : RealFunction I) (tree : QueryTree I) (path : List Bool) : ℝ :=
  ((treeCell tree path).card : ℝ)⁻¹ *
    (treeCell tree path).sum f

def treeConditionalVariance {I : Type*} [Fintype I]
    (f : RealFunction I) (tree : QueryTree I) (path : List Bool) : ℝ :=
  let μ := treeConditionalMean f tree path
  ((treeCell tree path).card : ℝ)⁻¹ *
    (treeCell tree path).sum (fun x => (f x - μ) ^ 2)

def treeInternalPaths {I : Type*} [Fintype I]
    (tree : QueryTree I) : Finset (List Bool) :=
  (treePaths tree).filter (fun path => (treeQueryAt tree path).isSome)

def treeArea {I : Type*} [Fintype I]
    (f : RealFunction I) (tree : QueryTree I) : ℝ :=
  (treeInternalPaths tree).sum
    (fun path => treeProbability tree path *
      treeConditionalVariance f tree path)

def freshFrom {I : Type*} [Fintype I]
    (seen : Finset I) : QueryTree I → Prop
  | .leaf _ => True
  | .query coordinate negative positive =>
      coordinate ∉ seen ∧
        freshFrom (insert coordinate seen) negative ∧
          freshFrom (insert coordinate seen) positive

def freshTree {I : Type*} [Fintype I] (tree : QueryTree I) : Prop :=
  freshFrom ∅ tree

def determines {I : Type*}
    (f : RealFunction I) (tree : QueryTree I) : Prop :=
  ∀ x, treeRun tree x = f x

def legalPolicy {I : Type*} [Fintype I]
    (f : RealFunction I) (tree : QueryTree I) : Prop :=
  freshTree tree ∧ determines f tree

noncomputable def minimumArea {I : Type*} [Fintype I]
    (f : RealFunction I) : ℝ :=
  sInf {a : ℝ |
    ∃ tree : QueryTree I, legalPolicy f tree ∧ a = treeArea f tree}

abbrev Remaining (I : Type*) (i : I) := {j : I // j ≠ i}

def insertFixed {I : Type*} [Fintype I]
    (i : I) (b : Bool) (x : Cube (Remaining I i)) : Cube I :=
  fun j => if h : j = i then b else x ⟨j, h⟩

def restrictReal {I : Type*} [Fintype I]
    (f : RealFunction I) (i : I) (b : Bool) :
    RealFunction (Remaining I i) :=
  fun x => f (insertFixed i b x)

noncomputable def areaSaving {I : Type*} [Fintype I]
    (f : RealFunction I) (i : I) : ℝ :=
  minimumArea f -
    (minimumArea (restrictReal f i false) +
      minimumArea (restrictReal f i true)) / 2

def walshCharacter {I : Type*}
    (S : Finset I) (x : Cube I) : ℝ :=
  S.prod (fun i => signValue (x i))

noncomputable def walshCoefficient {I : Type*} [Fintype I]
    (f : RealFunction I) (S : Finset I) : ℝ :=
  cubeMean (fun x => f x * walshCharacter S x)

noncomputable def shapleyEnergy {I : Type*} [Fintype I]
    (f : RealFunction I) (i : I) : ℝ :=
  ∑ S : Finset I,
    if S.Nonempty ∧ i ∈ S then
      walshCoefficient f S ^ 2 / (S.card : ℝ)
    else 0

noncomputable def pointwiseLoad {I : Type*} [Fintype I]
    (f : RealFunction I) : ℝ :=
  ∑ i : I,
    if 0 < shapleyEnergy f i then
      shapleyEnergy f i / areaSaving f i
    else 0

noncomputable def supportwiseLoad {I : Type*} [Fintype I]
    (f : RealFunction I) : ℝ :=
  ∑ S : Finset I,
    if S.Nonempty then
      (S.card : ℝ) * walshCoefficient f S ^ 2 /
        S.sum (fun i => areaSaving f i)
    else 0

def areaSavingsNonnegative : Prop :=
  ∀ (I : Type) [Fintype I] (f : RealFunction I) (i : I),
    0 ≤ areaSaving f i

def shapleyEnergyParseval : Prop :=
  ∀ (I : Type) [Fintype I] (f : RealFunction I),
    ∑ i : I, shapleyEnergy f i = cubeVariance f

def coordSize : ℕ → ℕ
  | 0 => 1
  | t + 1 => 1 + coordSize t + coordSize t

def rootCoordinate (t : ℕ) : Fin (1 + coordSize t + coordSize t) :=
  Fin.castLE
    (Nat.le_trans (Nat.le_add_right 1 (coordSize t))
      (Nat.le_add_right (1 + coordSize t) (coordSize t))) 0

def leftCoordinate (t : ℕ) (i : Fin (coordSize t)) :
    Fin (1 + coordSize t + coordSize t) :=
  Fin.castLE (Nat.le_add_right (1 + coordSize t) (coordSize t))
    (Fin.natAdd 1 i)

def rightCoordinate (t : ℕ) (i : Fin (coordSize t)) :
    Fin (1 + coordSize t + coordSize t) :=
  Fin.natAdd (1 + coordSize t) i

def relabel {I J : Type*} (r : I → J) : QueryTree I → QueryTree J
  | .leaf value => .leaf value
  | .query coordinate negative positive =>
      .query (r coordinate) (relabel r negative) (relabel r positive)

def selectorTree : (t : ℕ) → QueryTree (Fin (coordSize t))
  | 0 => .query (0 : Fin 1) (.leaf (-1)) (.leaf 1)
  | t + 1 =>
      .query (rootCoordinate t)
        (relabel (leftCoordinate t) (selectorTree t))
        (relabel (rightCoordinate t) (selectorTree t))

def selectorFunction (t : ℕ) : RealFunction (Fin (coordSize t)) :=
  treeRun (selectorTree t)

def treeQueryCoordinates {I : Type*} :
    QueryTree I → List Bool → List I
  | .leaf _, _ => []
  | .query coordinate _ _, [] => [coordinate]
  | .query coordinate negative positive, branch :: path =>
      coordinate ::
        treeQueryCoordinates (if branch then positive else negative) path

def selectorInternalPaths (t : ℕ) : Finset (List Bool) :=
  (treeInternalPaths (selectorTree t)).filter (fun path => path.length < t)

def selectorLeafPaths (t : ℕ) : Finset (List Bool) :=
  (treeInternalPaths (selectorTree t)).filter (fun path => path.length = t)

def pathInternalCoordinates (t : ℕ) (path : List Bool) :
    Finset (Fin (coordSize t)) :=
  (treeQueryCoordinates (selectorTree t) path).take t |>.toFinset

def selectorInternalCoordinate (t : ℕ) (v : Fin (coordSize t)) : Prop :=
  ∃ path, path ∈ selectorInternalPaths t ∧
    treeQueryAt (selectorTree t) path = some v

def selectorLeafCoordinate (t : ℕ) (v : Fin (coordSize t)) : Prop :=
  ∃ path, path ∈ selectorLeafPaths t ∧
    treeQueryAt (selectorTree t) path = some v

def selectorCoordinatesPrivate (t : ℕ) : Prop :=
  (∀ v, selectorInternalCoordinate t v ∨ selectorLeafCoordinate t v) ∧
    (∀ v, ¬ (selectorInternalCoordinate t v ∧ selectorLeafCoordinate t v)) ∧
    (∀ p q,
      p ∈ treeInternalPaths (selectorTree t) →
      q ∈ treeInternalPaths (selectorTree t) →
      treeQueryAt (selectorTree t) p = treeQueryAt (selectorTree t) q →
      p = q)

def selectorValid (t : ℕ) : Prop :=
  freshTree (selectorTree t) ∧
    determines (selectorFunction t) (selectorTree t) ∧
    treeDepth (selectorTree t) = t + 1 ∧
    coordSize t = 2 ^ (t + 1) - 1 ∧
    selectorCoordinatesPrivate t

def selectorSupport (t : ℕ) (S : Finset (Fin (coordSize t))) : Prop :=
  ∃ path, path ∈ selectorLeafPaths t ∧
    ∃ l, treeQueryAt (selectorTree t) path = some l ∧
      ∃ T : Finset (Fin (coordSize t)),
        T ⊆ pathInternalCoordinates t path ∧ S = T ∪ {l}

def inversePowerTwo (j : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ j

def selectorLeafSavingFormula (t : ℕ) : ℝ :=
  ((2 : ℝ) ^ (t + 1) - 1) / (4 : ℝ) ^ t

def selectorLeafShapleyFormula (t : ℕ) : ℝ :=
  ((2 : ℝ) ^ (t + 1) - 1) /
    ((4 : ℝ) ^ t * ((t + 1 : ℕ) : ℝ))

def selectorLeafKFormula (t : ℕ) : ℝ :=
  (2 : ℝ) ^ t / ((t + 1 : ℕ) : ℝ)

def selectorSupportwiseFormula (t : ℕ) : ℝ :=
  ((t + 2 : ℕ) : ℝ) / 6

def selectorSavingsExact (t : ℕ) : Prop :=
  (∀ (j : ℕ) (path : List Bool),
    path ∈ selectorInternalPaths t →
      path.length = j →
        ∀ v, treeQueryAt (selectorTree t) path = some v →
          areaSaving (selectorFunction t) v = inversePowerTwo j) ∧
    (∀ l, selectorLeafCoordinate t l →
      areaSaving (selectorFunction t) l = selectorLeafSavingFormula t)

def selectorSpectrumExact (t : ℕ) : Prop :=
  (∀ S : Finset (Fin (coordSize t)),
    walshCoefficient (selectorFunction t) S ≠ 0 ↔ selectorSupport t S) ∧
    (∀ S : Finset (Fin (coordSize t)), selectorSupport t S →
      |walshCoefficient (selectorFunction t) S| = inversePowerTwo t) ∧
    (∀ v, selectorInternalCoordinate t v →
      walshCoefficient (selectorFunction t) {v} = 0) ∧
    (∀ l, selectorLeafCoordinate t l →
      |walshCoefficient (selectorFunction t) {l}| = inversePowerTwo t)

def selectorLeafLoadExact (t : ℕ) : Prop :=
  (∀ l, selectorLeafCoordinate t l →
    shapleyEnergy (selectorFunction t) l = selectorLeafShapleyFormula t ∧
      shapleyEnergy (selectorFunction t) l /
          areaSaving (selectorFunction t) l = 1 / ((t + 1 : ℕ) : ℝ)) ∧
    pointwiseLoad (selectorFunction t) ≥ selectorLeafKFormula t

def selectorSupportwiseLoadExact (t : ℕ) : Prop :=
  supportwiseLoad (selectorFunction t) ≥ selectorSupportwiseFormula t

def booleanKUniformBound : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (f : RealFunction (Fin n)),
    booleanValued f → pointwiseLoad f ≤ C

def booleanLUniformBound : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (f : RealFunction (Fin n)),
    booleanValued f → supportwiseLoad f ≤ C

def booleanKUnbounded : Prop :=
  ∀ C : ℝ, ∃ (n : ℕ) (f : RealFunction (Fin n)),
    booleanValued f ∧ C < pointwiseLoad f

def booleanLUnbounded : Prop :=
  ∀ C : ℝ, ∃ (n : ℕ) (f : RealFunction (Fin n)),
    booleanValued f ∧ C < supportwiseLoad f

def selectorKUnbounded : Prop :=
  ∀ C : ℝ, ∃ t : ℕ, 1 ≤ t ∧ C < pointwiseLoad (selectorFunction t)

def selectorLUnbounded : Prop :=
  ∀ C : ℝ, ∃ t : ℕ, 1 ≤ t ∧ C < supportwiseLoad (selectorFunction t)

def claim61316 : Prop :=
  areaSavingsNonnegative ∧
    shapleyEnergyParseval ∧
    (∀ t : ℕ, 1 ≤ t →
      selectorValid t ∧
        booleanValued (selectorFunction t) ∧
        minimumArea (selectorFunction t) = ((t + 1 : ℕ) : ℝ) ∧
        selectorSavingsExact t ∧
        selectorSpectrumExact t ∧
        selectorLeafLoadExact t ∧
        selectorSupportwiseLoadExact t) ∧
    booleanKUnbounded ∧
    booleanLUnbounded ∧
    selectorKUnbounded ∧
    selectorLUnbounded ∧
    ¬ booleanKUniformBound ∧
    ¬ booleanLUniformBound

end
end MathlibPlus.Open.ResearchFormalization.OracleAreaSelectorLoadDivergenceClaim61316
