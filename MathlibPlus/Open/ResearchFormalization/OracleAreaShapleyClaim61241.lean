import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaShapleyClaim61241

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev Cube (I : Type*) := I → Bool
abbrev BooleanTarget (I : Type*) := Cube I → Bool


def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

def booleanAsReal {I : Type*} (h : BooleanTarget I) : Cube I → ℝ :=
  fun x => signValue (h x)

def cubeAverage {I : Type*} [Fintype I] (f : Cube I → ℝ) : ℝ :=
  (Fintype.card (Cube I) : ℝ)⁻¹ * ∑ x, f x

def cubeVariance {I : Type*} [Fintype I] (f : Cube I → ℝ) : ℝ :=
  let μ := cubeAverage f
  cubeAverage (fun x => (f x - μ) ^ 2)

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

def treeAt {I : Type*} : QueryTree I → List Bool → Option (QueryTree I)
  | tree, [] => some tree
  | .leaf _, _ :: _ => none
  | .query _ negative positive, branch :: rest =>
      if branch then treeAt positive rest else treeAt negative rest

def treeQueryAt {I : Type*} : QueryTree I → List Bool → Option I
  | .leaf _, _ => none
  | .query coordinate _ _, [] => some coordinate
  | .query _ negative positive, branch :: rest =>
      if branch then treeQueryAt positive rest else treeQueryAt negative rest

def treeFollows {I : Type*} : QueryTree I → Cube I → List Bool → Prop
  | _, _, [] => True
  | .leaf _, _, _ :: _ => False
  | .query coordinate negative positive, x, branch :: rest =>
      if x coordinate = branch then
        if branch then treeFollows positive x rest
        else treeFollows negative x rest
      else False

noncomputable def treeCell {I : Type*} [Fintype I]
    (tree : QueryTree I) (path : List Bool) : Finset (Cube I) :=
  Finset.univ.filter (fun x => treeFollows tree x path)

def treeProbability {I : Type*} [Fintype I]
    (tree : QueryTree I) (path : List Bool) : ℝ :=
  (treeCell tree path).card / (Fintype.card (Cube I) : ℝ)

def treeConditionalMean {I : Type*} [Fintype I]
    (f : Cube I → ℝ) (tree : QueryTree I) (path : List Bool) : ℝ :=
  ((treeCell tree path).card : ℝ)⁻¹ *
    (treeCell tree path).sum f

def treeConditionalVariance {I : Type*} [Fintype I]
    (f : Cube I → ℝ) (tree : QueryTree I) (path : List Bool) : ℝ :=
  let μ := treeConditionalMean f tree path
  ((treeCell tree path).card : ℝ)⁻¹ *
    (treeCell tree path).sum (fun x => (f x - μ) ^ 2)

def treeInternalPaths {I : Type*} [Fintype I]
    (tree : QueryTree I) : Finset (List Bool) :=
  (treePaths tree).filter (fun path => (treeQueryAt tree path).isSome)

def treeArea {I : Type*} [Fintype I]
    (f : Cube I → ℝ) (tree : QueryTree I) : ℝ :=
  (treeInternalPaths tree).sum
    (fun path => treeProbability tree path * treeConditionalVariance f tree path)

def freshFrom {I : Type*} [Fintype I]
    (seen : Finset I) : QueryTree I → Prop
  | .leaf _ => True
  | .query coordinate negative positive =>
      coordinate ∉ seen ∧
        freshFrom (insert coordinate seen) negative ∧
          freshFrom (insert coordinate seen) positive

def freshTree {I : Type*} [Fintype I] (tree : QueryTree I) : Prop :=
  freshFrom ∅ tree

def determinesReal {I : Type*}
    (f : Cube I → ℝ) (tree : QueryTree I) : Prop :=
  ∀ x, treeRun tree x = f x

def determinesBoolean {I : Type*}
    (h : BooleanTarget I) (tree : QueryTree I) : Prop :=
  ∀ x, treeRun tree x = signValue (h x)

noncomputable def minimumArea {I : Type*} [Fintype I]
    (f : Cube I → ℝ) : ℝ :=
  sInf {a : ℝ |
    ∃ tree : QueryTree I,
      freshTree tree ∧ determinesReal f tree ∧ a = treeArea f tree}

def minimumBooleanArea {I : Type*} [Fintype I]
    (h : BooleanTarget I) : ℝ :=
  minimumArea (booleanAsReal h)

abbrev Remaining (I : Type*) (i : I) := {j : I // j ≠ i}

def insertFixed {I : Type*} [Fintype I]
    (i : I) (b : Bool) (y : Cube (Remaining I i)) : Cube I :=
  fun j => if h : j = i then b else y ⟨j, h⟩

def restrictBoolean {I : Type*} [Fintype I]
    (h : BooleanTarget I) (i : I) (b : Bool) :
    BooleanTarget (Remaining I i) :=
  fun y => h (insertFixed i b y)

def restrictReal {I : Type*} [Fintype I]
    (f : Cube I → ℝ) (i : I) (b : Bool) :
    Cube (Remaining I i) → ℝ :=
  fun y => f (insertFixed i b y)

def areaSaving {I : Type*} [Fintype I]
    (h : BooleanTarget I) (i : I) : ℝ :=
  minimumBooleanArea h -
    (minimumArea (restrictReal (booleanAsReal h) i false) +
      minimumArea (restrictReal (booleanAsReal h) i true)) / 2

def walshCharacter {I : Type*}
    (S : Finset I) (x : Cube I) : ℝ :=
  S.prod (fun i => signValue (x i))

def walshCoefficient {I : Type*} [Fintype I]
    (f : Cube I → ℝ) (S : Finset I) : ℝ :=
  cubeAverage (fun x => f x * walshCharacter S x)

def shapleyEnergy {I : Type*} [Fintype I]
    (f : Cube I → ℝ) (i : I) : ℝ :=
  ∑ S : Finset I,
    if S.Nonempty ∧ i ∈ S then
      walshCoefficient f S ^ 2 / (S.card : ℝ)
    else 0

def shapleyPolarization {I : Type*} [Fintype I]
    (f u : Cube I → ℝ) (i : I) : ℝ :=
  ∑ S : Finset I,
    if S.Nonempty ∧ i ∈ S then
      walshCoefficient f S * walshCoefficient u S / (S.card : ℝ)
    else 0

def covariance {I : Type*} [Fintype I]
    (f u : Cube I → ℝ) : ℝ :=
  cubeAverage
    (fun x => (f x - cubeAverage f) * (u x - cubeAverage u))

def KValue {I : Type*} [Fintype I]
    (h : BooleanTarget I) : ℝ :=
  ∑ i : I,
    if shapleyEnergy (booleanAsReal h) i = 0 ∧ areaSaving h i = 0 then
      0
    else shapleyEnergy (booleanAsReal h) i / areaSaving h i

def TargetClass :=
  ∀ (I : Type) [Fintype I], BooleanTarget I → Prop

def classClosedUnderRestriction (Klass : TargetClass) : Prop :=
  ∀ (I : Type) [Fintype I] (h : BooleanTarget I),
    Klass I h →
      ∀ (i : I) (b : Bool),
        Klass (Remaining I i) (restrictBoolean h i b)

def classKBound (Klass : TargetClass) (C : ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] (h : BooleanTarget I),
    Klass I h → KValue h ≤ C

def suppliedAtRoot {I : Type*} [Fintype I]
    (h : BooleanTarget I) (k : ℕ) : Prop :=
  ∃ tree : QueryTree I,
    freshTree tree ∧ treeDepth tree ≤ k ∧ determinesBoolean h tree

def probabilityWeights {m : ℕ} (w : Fin m → ℝ) : Prop :=
  (∀ r, 0 ≤ w r) ∧ ∑ r, w r = 1

def mixtureBarycenter {I : Type*} {m : ℕ}
    (w : Fin m → ℝ) (H : Fin m → BooleanTarget I) : Cube I → ℝ :=
  fun x => ∑ r, w r * signValue (H r x)

def treeTranscript {I : Type*}
    : QueryTree I → List Bool → List (I × Bool)
  | .leaf _, _ => []
  | .query _ _ _, [] => []
  | .query coordinate negative positive, branch :: rest =>
      (coordinate, branch) ::
        treeTranscript (if branch then positive else negative) rest

def treeSeen {I : Type*} [Fintype I]
    (tree : QueryTree I) (path : List Bool) : Finset I :=
  (treeTranscript tree path).map Prod.fst |>.toFinset

def pathValue {I : Type*} [Fintype I]
    : List (I × Bool) → I → Bool
  | [], _ => false
  | (coordinate, value) :: rest, i =>
      if i = coordinate then value else pathValue rest i

abbrev PathRemaining {I : Type*} [Fintype I]
    (tree : QueryTree I) (path : List Bool) :=
  {j : I // j ∉ treeSeen tree path}

def pathLift {I : Type*} [Fintype I]
    (tree : QueryTree I) (path : List Bool)
    (y : Cube (PathRemaining tree path)) : Cube I :=
  fun j =>
    if h : j ∈ treeSeen tree path then
      pathValue (treeTranscript tree path) j
    else
      y ⟨j, h⟩

def pathRestrictReal {I : Type*} [Fintype I]
    (f : Cube I → ℝ) (tree : QueryTree I) (path : List Bool) :
    Cube (PathRemaining tree path) → ℝ :=
  fun y => f (pathLift tree path y)

def pathRestrictBoolean {I : Type*} [Fintype I]
    (h : BooleanTarget I) (tree : QueryTree I) (path : List Bool) :
    BooleanTarget (PathRemaining tree path) :=
  fun y => h (pathLift tree path y)

def pathAverageSaving {I : Type*} [Fintype I] {m : ℕ}
    (w : Fin m → ℝ) (H : Fin m → BooleanTarget I)
    (tree : QueryTree I) (path : List Bool)
    (q : PathRemaining tree path) : ℝ :=
  ∑ r, w r *
    areaSaving (pathRestrictBoolean (H r) tree path) q

def pathBarycenter {I : Type*} [Fintype I] {m : ℕ}
    (w : Fin m → ℝ) (H : Fin m → BooleanTarget I)
    (tree : QueryTree I) (path : List Bool) :
    Cube (PathRemaining tree path) → ℝ :=
  fun y => ∑ r, w r *
    signValue ((pathRestrictBoolean (H r) tree path) y)

def barycenterConstantOnPath {I : Type*} [Fintype I] {m : ℕ}
    (w : Fin m → ℝ) (H : Fin m → BooleanTarget I)
    (tree : QueryTree I) (path : List Bool) : Prop :=
  ∀ x y : Cube (PathRemaining tree path),
    pathBarycenter w H tree path x = pathBarycenter w H tree path y

def maximizingMixturePolicy {I : Type*} [Fintype I] {m : ℕ}
    (w : Fin m → ℝ) (H : Fin m → BooleanTarget I)
    (tree : QueryTree I) : Prop :=
  ∀ path ∈ treeInternalPaths tree,
    ∃ q : PathRemaining tree path,
      treeQueryAt tree path = some q.1 ∧
        ∀ j : PathRemaining tree path,
          pathAverageSaving w H tree path q ≥
            pathAverageSaving w H tree path j

def stopsExactlyAtMeasurability {I : Type*} [Fintype I] {m : ℕ}
    (w : Fin m → ℝ) (H : Fin m → BooleanTarget I)
    (tree : QueryTree I) : Prop :=
  ∀ path ∈ treePaths tree,
    (treeQueryAt tree path).isSome ↔
      ¬ barycenterConstantOnPath w H tree path

def deterministicMixturePolicy {I : Type*} [Fintype I] {m : ℕ}
    (w : Fin m → ℝ) (H : Fin m → BooleanTarget I)
    (tree : QueryTree I) : Prop :=
  freshTree tree ∧
    determinesReal (mixtureBarycenter w H) tree ∧
    maximizingMixturePolicy w H tree ∧
    stopsExactlyAtMeasurability w H tree

def pointwiseShapleyReduction : Prop :=
  ∀ (I : Type) [Fintype I] (C : ℝ) (Klass : TargetClass),
    classClosedUnderRestriction Klass →
      classKBound Klass C →
        ∀ (k m : ℕ) (w : Fin m → ℝ)
          (H : Fin m → BooleanTarget I),
          probabilityWeights w →
            (∀ r : Fin m,
              Klass I (H r) ∧ suppliedAtRoot (H r) k) →
              ∃ tree : QueryTree I,
                deterministicMixturePolicy w H tree ∧
                  treeArea (mixtureBarycenter w H) tree ≤ C * (k : ℝ)

def specialBoolean (m : ℕ) : BooleanTarget (Fin (m + 1)) :=
  fun x =>
    if x (Fin.last m) = false ∧
        ¬ (∀ i : Fin m, x (Fin.castSucc i) = true) then
      true
    else false

def specialM (m : ℕ) : ℝ := (2 ^ m : ℕ)

def specialTarget (m : ℕ) : Cube (Fin (m + 1)) → ℝ :=
  booleanAsReal (specialBoolean m)

def specialVarianceFormula (m : ℕ) : ℝ :=
  1 - (specialM m)⁻¹ ^ 2

def specialAreaFormula (m : ℕ) : ℝ :=
  1 + 2 * (m : ℝ) / specialM m -
    (2 * specialM m - 1) / (specialM m) ^ 2

def specialLowerSavingFormula (m : ℕ) : ℝ :=
  (2 * specialM m - 1) / (specialM m) ^ 2

def specialTopSavingFormula (m : ℕ) : ℝ :=
  1 - (specialM m)⁻¹ ^ 2

def specialLowerShapleyFormula (m : ℕ) : ℝ :=
  (2 * specialM m - 1) / ((m + 1 : ℕ) : ℝ) / (specialM m) ^ 2

def specialTopShapleyFormula (m : ℕ) : ℝ :=
  (1 - (specialM m)⁻¹) ^ 2 +
    (specialM m)⁻¹ ^ 2 *
      ((2 * specialM m - 1) / ((m + 1 : ℕ) : ℝ) - 1)

def specialK (m : ℕ) : ℝ :=
  KValue (specialBoolean m)

def lowerCharacter (m : ℕ) (S : Finset (Fin m))
    (x : Cube (Fin (m + 1))) : ℝ :=
  S.prod (fun i => signValue (x (Fin.castSucc i)))

def specialWalshExpansion (m : ℕ) : Prop :=
  ∀ x : Cube (Fin (m + 1)),
    specialTarget m x =
      -signValue (x (Fin.last m)) -
        (specialM m)⁻¹ * ∑ S : Finset (Fin m), lowerCharacter m S x +
        (specialM m)⁻¹ *
          ∑ S : Finset (Fin m),
            signValue (x (Fin.last m)) * lowerCharacter m S x

def specialBranchArea (m : ℕ) : ℝ :=
  ∑ t : Fin m,
    ((2 : ℝ)⁻¹) ^ t.1 *
      (4 * ((2 : ℝ) ^ (m - t.1) - 1) /
        (2 : ℝ) ^ (2 * (m - t.1)))

def specialSymmetrySum (m : ℕ) (i : Fin m) : ℝ :=
  ∑ S : Finset (Fin (m + 1)),
    if Fin.castSucc i ∈ S then (S.card : ℝ)⁻¹ else 0

def specialBenchmark : Prop :=
  (∀ m : ℕ, 1 ≤ m →
    cubeVariance (specialTarget m) = specialVarianceFormula m ∧
    minimumArea (specialTarget m) = specialAreaFormula m ∧
    minimumArea (specialTarget m) =
      cubeVariance (specialTarget m) + specialBranchArea m / 2 ∧
    (∀ i : Fin m,
      areaSaving (specialBoolean m) (Fin.castSucc i) =
        specialLowerSavingFormula m) ∧
    areaSaving (specialBoolean m) (Fin.last m) =
      specialTopSavingFormula m ∧
    (∀ i : Fin m,
      shapleyEnergy (specialTarget m) (Fin.castSucc i) =
        specialLowerShapleyFormula m) ∧
    shapleyEnergy (specialTarget m) (Fin.last m) =
      specialTopShapleyFormula m ∧
    specialK m =
      (m : ℝ) / ((m + 1 : ℕ) : ℝ) +
        specialTopShapleyFormula m / specialTopSavingFormula m ∧
    specialK m < 2 ∧
    2 - specialK m =
      ((specialM m) ^ 2 + 2 * specialM m * (m + 1 : ℕ) -
          2 * specialM m - (m + 1 : ℕ)) /
        (((m + 1 : ℕ) : ℝ) * (specialM m - 1) *
          (specialM m + 1)) ∧
    2 - specialK m > 0 ∧
    specialBranchArea m =
      4 * (m : ℝ) / specialM m -
        4 * (specialM m - 1) / (specialM m) ^ 2 ∧
    (∀ i : Fin m,
      specialSymmetrySum m i =
        ((2 : ℝ) ^ (m + 1) - 1) / ((m + 1 : ℕ) : ℝ)) ∧
    specialWalshExpansion m) ∧
  Filter.Tendsto (fun m => 2 - specialK m) Filter.atTop (nhds 0) ∧
  sSup {q : ℝ | ∃ m : ℕ, 1 ≤ m ∧ q = specialK m} = 2

def claim61241 : Prop :=
  pointwiseShapleyReduction ∧ specialBenchmark

end
end MathlibPlus.Open.ResearchFormalization.OracleAreaShapleyClaim61241
