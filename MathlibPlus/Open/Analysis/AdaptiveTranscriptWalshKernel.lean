import Mathlib

namespace MathlibPlus.Open.Analysis

open MeasureTheory
open scoped BigOperators
noncomputable section
universe u v
attribute [local instance] Classical.decEq Classical.propDecidable

/-- A finite deterministic tree of coordinate reveals.  A `false` branch records
    the value `-1`, and a `true` branch records the value `1`. -/
inductive AdaptiveRevealTree (I : Type u) where
  | leaf (output : ℝ) : AdaptiveRevealTree I
  | query (coordinate : I)
      (negative positive : AdaptiveRevealTree I) : AdaptiveRevealTree I

/-- The depth of a reveal tree. -/
def adaptiveTreeDepth : AdaptiveRevealTree I → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      Nat.succ (max (adaptiveTreeDepth negative) (adaptiveTreeDepth positive))

/-- Paths are written from the root towards the node. -/
def adaptiveTreeNodes : AdaptiveRevealTree I → Finset (List Bool)
  | .leaf _ => {([] : List Bool)}
  | .query _ negative positive =>
      insert []
        ((adaptiveTreeNodes negative).image (fun p => false :: p) ∪
          (adaptiveTreeNodes positive).image (fun p => true :: p))

/-- The subtree reached by a path, when the path is valid. -/
def adaptiveTreeAt : AdaptiveRevealTree I → List Bool →
    Option (AdaptiveRevealTree I)
  | tree, [] => some tree
  | .leaf _, _ :: _ => none
  | .query _ negative positive, branch :: rest =>
      match branch with
      | false => adaptiveTreeAt negative rest
      | true => adaptiveTreeAt positive rest

/-- The coordinates and signs on a transcript path. -/
def adaptiveTreeTranscript : AdaptiveRevealTree I → List Bool → List (I × ℝ)
  | .leaf _, _ => []
  | .query _ _ _, [] => []
  | .query coordinate negative positive, branch :: rest =>
      match branch with
      | false => (coordinate, -1) :: adaptiveTreeTranscript negative rest
      | true => (coordinate, 1) :: adaptiveTreeTranscript positive rest

/-- The coordinates revealed on a path. -/
def adaptiveTreeRevealed (tree : AdaptiveRevealTree I) (path : List Bool) :
    Finset I :=
  (adaptiveTreeTranscript tree path).map Prod.fst |>.toFinset

/-- The cell selected by a transcript. -/
def adaptiveTreeCell (tree : AdaptiveRevealTree I) (path : List Bool) :
    Set (I → ℝ) :=
  {x | ∀ pair ∈ adaptiveTreeTranscript tree path, x pair.1 = pair.2}

/-- The value prescribed by a transcript, with an irrelevant default outside
    the revealed coordinates. -/
def adaptiveTreeTranscriptValue : AdaptiveRevealTree I → List Bool → I → ℝ
  | .leaf _, _, _ => 0
  | .query _ _ _, [], _ => 0
  | .query coordinate negative positive, branch :: rest, q =>
      match branch with
      | false =>
          if q = coordinate then -1
          else adaptiveTreeTranscriptValue negative rest q
      | true =>
          if q = coordinate then 1
          else adaptiveTreeTranscriptValue positive rest q

/-- Running a tree on an oracle. -/
def adaptiveTreeRun : AdaptiveRevealTree I → (I → ℝ) → ℝ
  | .leaf output, _ => output
  | .query coordinate negative positive, x =>
      if x coordinate = -1 then adaptiveTreeRun negative x
      else adaptiveTreeRun positive x

/-- The complete branch transcript produced by an oracle. -/
def adaptiveTreePath : AdaptiveRevealTree I → (I → ℝ) → List Bool
  | .leaf _, _ => []
  | .query coordinate negative positive, x =>
      if x coordinate = -1 then
        false :: adaptiveTreePath negative x
      else
        true :: adaptiveTreePath positive x

def adaptiveTreeTau (tree : AdaptiveRevealTree I) (x : I → ℝ) : ℕ :=
  (adaptiveTreePath tree x).length

/-- Legality means ±1 leaf outputs and no repeated coordinate along a path. -/
def legalAdaptiveTree (tree : AdaptiveRevealTree I) : Prop :=
  (∀ path ∈ adaptiveTreeNodes tree, ∀ output,
      adaptiveTreeAt tree path = some (.leaf output) →
        output = -1 ∨ output = 1) ∧
  (∀ path ∈ adaptiveTreeNodes tree, ∀ coordinate negative positive,
      adaptiveTreeAt tree path = some (.query coordinate negative positive) →
        coordinate ∉ (adaptiveTreeTranscript tree path).map Prod.fst)

def adaptiveTreeDescendant (ancestor descendant : List Bool) : Prop :=
  ∃ suffix, descendant = ancestor ++ suffix

def adaptiveCellProbability (P : Measure (I → ℝ)) (C : Set (I → ℝ)) : ℝ :=
  ENNReal.toReal (P C)

def adaptiveConditionalMean (P : Measure (I → ℝ)) (u : (I → ℝ) → ℝ)
    (C : Set (I → ℝ)) : ℝ :=
  (adaptiveCellProbability P C)⁻¹ * ∫ x in C, u x ∂P

def adaptiveConditionalVariance (P : Measure (I → ℝ)) (u : (I → ℝ) → ℝ)
    (C : Set (I → ℝ)) : ℝ :=
  (adaptiveCellProbability P C)⁻¹ *
    ∫ x in C, (u x - adaptiveConditionalMean P u C) ^ 2 ∂P

def adaptiveVariance (P : Measure (I → ℝ)) (u : (I → ℝ) → ℝ) : ℝ :=
  adaptiveConditionalVariance P u Set.univ

def adaptiveConditionalCellWeight (P : Measure (I → ℝ))
    (tree : AdaptiveRevealTree I) (ancestor descendant : List Bool) : ℝ :=
  adaptiveCellProbability P (adaptiveTreeCell tree descendant) /
    adaptiveCellProbability P (adaptiveTreeCell tree ancestor)

/-- The exact posterior-variance potential, including the node itself. -/
def adaptiveHarmonicPotential (P : Measure (I → ℝ))
    (tree : AdaptiveRevealTree I) (u : (I → ℝ) → ℝ) (path : List Bool) : ℝ :=
  ∑ descendant ∈ ((adaptiveTreeNodes tree).filter
      (adaptiveTreeDescendant path)),
    adaptiveConditionalCellWeight P tree path descendant *
      adaptiveConditionalVariance P u (adaptiveTreeCell tree descendant)

/-- The root quadratic seminorm. -/
def adaptiveRootSeminormSq (P : Measure (I → ℝ))
    (tree : AdaptiveRevealTree I) (u : (I → ℝ) → ℝ) : ℝ :=
  ∑ path ∈ adaptiveTreeNodes tree,
    adaptiveCellProbability P (adaptiveTreeCell tree path) *
      adaptiveConditionalVariance P u (adaptiveTreeCell tree path)

def adaptiveTranscriptRho (tree : AdaptiveRevealTree I) (path : List Bool) : ℝ :=
  ((2 : ℝ)⁻¹) ^ (adaptiveTreeRevealed tree path).card

/-- Finite-dimensional cylinder probabilities for independent fair signs. -/
def fairIndependentRademacher (P : Measure (I → ℝ)) : Prop :=
  P Set.univ = 1 ∧
    ∀ (coordinates : Finset I) (signs : I → ℝ),
      (∀ i ∈ coordinates, signs i = -1 ∨ signs i = 1) →
        P {x | ∀ i ∈ coordinates, x i = signs i} =
          ((2 : ENNReal)⁻¹) ^ coordinates.card

def adaptiveWalshCharacter (A : Finset I) (x : I → ℝ) : ℝ :=
  ∏ i ∈ A, x i

def adaptiveWalshPolynomial (a : Finset I →₀ ℝ) (x : I → ℝ) : ℝ :=
  ∑ A ∈ a.support, a A * adaptiveWalshCharacter A x

def adaptiveTreeTranscriptCharacter (tree : AdaptiveRevealTree I)
    (path : List Bool) (A : Finset I) : ℝ :=
  ∏ i ∈ A, adaptiveTreeTranscriptValue tree path i

/-- The local Walsh coefficient on a transcript cell. -/
def adaptiveLocalWalshCoefficient (a : Finset I →₀ ℝ)
    (tree : AdaptiveRevealTree I) (path : List Bool) (S : Finset I) : ℝ :=
  ∑ B ∈ (adaptiveTreeRevealed tree path).powerset,
    a (S ∪ B) * adaptiveTreeTranscriptCharacter tree path B

/-- The local Walsh variance of a finite Walsh polynomial. -/
def adaptiveLocalWalshVariance [Countable I] (a : Finset I →₀ ℝ)
    (tree : AdaptiveRevealTree I) (path : List Bool) : ℝ :=
  ∑' S : Finset I,
    if S.Nonempty ∧ Disjoint S (adaptiveTreeRevealed tree path) then
      (adaptiveLocalWalshCoefficient a tree path S) ^ 2
    else 0

def adaptiveWalshPotential [Countable I] (a : Finset I →₀ ℝ)
    (tree : AdaptiveRevealTree I) (path : List Bool) : ℝ :=
  ∑ descendant ∈ ((adaptiveTreeNodes tree).filter
      (adaptiveTreeDescendant path)),
    ((2 : ℝ)⁻¹) ^
        ((adaptiveTreeRevealed tree descendant).card -
          (adaptiveTreeRevealed tree path).card) *
      adaptiveLocalWalshVariance a tree descendant

/-- The adaptive Walsh kernel matrix. -/
def adaptiveWalshKernel (tree : AdaptiveRevealTree I)
    (A B : Finset I) : ℝ :=
  ∑ path ∈ (adaptiveTreeNodes tree).filter (fun path =>
      A \ adaptiveTreeRevealed tree path =
          B \ adaptiveTreeRevealed tree path ∧
        (A \ adaptiveTreeRevealed tree path).Nonempty),
    adaptiveTranscriptRho tree path *
      (∏ i ∈ A ∩ adaptiveTreeRevealed tree path,
        adaptiveTreeTranscriptValue tree path i) *
      (∏ i ∈ B ∩ adaptiveTreeRevealed tree path,
        adaptiveTreeTranscriptValue tree path i)

def adaptiveFiniteWalshQuadraticForm (tree : AdaptiveRevealTree I)
    (a : Finset I →₀ ℝ) : ℝ :=
  ∑ A ∈ a.support, ∑ B ∈ a.support,
    a A * adaptiveWalshKernel tree A B * a B

def adaptiveL2Norm (P : Measure (I → ℝ)) (u : (I → ℝ) → ℝ) : ℝ :=
  Real.sqrt (∫ x, (u x) ^ 2 ∂P)

/-- A precise bounded-quadratic-form interpretation of the infinite Walsh
    formula.  Finite Walsh polynomials determine the form, and every
    L²-convergent finite-polynomial approximation has the stated limit. -/
def adaptiveBoundedWalshQuadraticLimit [Countable I]
    (P : Measure (I → ℝ)) (tree : AdaptiveRevealTree I)
    (u : (I → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ a : Finset I →₀ ℝ,
      |adaptiveFiniteWalshQuadraticForm tree a| ≤
        C * (adaptiveL2Norm P (adaptiveWalshPolynomial a)) ^ 2) ∧
    ∀ a : ℕ → (Finset I →₀ ℝ),
      Filter.Tendsto
          (fun n => adaptiveL2Norm P
            (fun x => adaptiveWalshPolynomial (a n) x - u x))
          Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => adaptiveFiniteWalshQuadraticForm tree (a n))
          Filter.atTop (nhds (adaptiveRootSeminormSq P tree u)) ∧
    ∃ a : ℕ → (Finset I →₀ ℝ),
      Filter.Tendsto
          (fun n => adaptiveL2Norm P
            (fun x => adaptiveWalshPolynomial (a n) x - u x))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun n => adaptiveFiniteWalshQuadraticForm tree (a n))
          Filter.atTop (nhds (adaptiveRootSeminormSq P tree u))

def adaptiveExpectedTranscriptReward (P : Measure (I → ℝ))
    (tree : AdaptiveRevealTree I) (g : (I → ℝ) → ℝ) : ℝ :=
  ∫ x,
    (∑ t ∈ Finset.range (adaptiveTreeTau tree x + 1),
      adaptiveConditionalVariance P g
        (adaptiveTreeCell tree ((adaptiveTreePath tree x).take t))) ∂P

/-- The filtration cell after `t` reveals on the path generated by `x`. -/
def adaptiveTranscriptFiltrationCell (tree : AdaptiveRevealTree I)
    (x : I → ℝ) (t : ℕ) : Set (I → ℝ) :=
  adaptiveTreeCell tree ((adaptiveTreePath tree x).take t)

/-- The complete potential statement for one selected legal component. -/
def adaptiveTranscriptPotentialStatement [Countable I]
    (P : Measure (I → ℝ)) (tree : AdaptiveRevealTree I) (k : ℕ)
    (g : (I → ℝ) → ℝ) : Prop :=
  legalAdaptiveTree tree ∧ adaptiveTreeDepth tree ≤ k ∧
  (∀ path ∈ adaptiveTreeNodes tree,
    adaptiveCellProbability P (adaptiveTreeCell tree path) =
      adaptiveTranscriptRho tree path) ∧
  (∀ u : (I → ℝ) → ℝ, MemLp u 2 P →
    (∀ path ∈ adaptiveTreeNodes tree, ∀ coordinate negative positive,
      adaptiveTreeAt tree path = some (.query coordinate negative positive) →
        adaptiveHarmonicPotential P tree u path =
          adaptiveConditionalVariance P u (adaptiveTreeCell tree path) +
            (adaptiveHarmonicPotential P tree u (path ++ [false]) +
              adaptiveHarmonicPotential P tree u (path ++ [true])) / 2) ∧
    (∀ path ∈ adaptiveTreeNodes tree, ∀ output,
      adaptiveTreeAt tree path = some (.leaf output) →
        adaptiveHarmonicPotential P tree u path =
          adaptiveConditionalVariance P u (adaptiveTreeCell tree path)) ∧
    adaptiveVariance P u ≤ adaptiveRootSeminormSq P tree u ∧
    adaptiveRootSeminormSq P tree u ≤
      (k + 1 : ℝ) * adaptiveVariance P u ∧
    (∀ c : ℝ,
      adaptiveRootSeminormSq P tree (fun _ => c) = 0)) ∧
  (∀ a : Finset I →₀ ℝ, ∀ path ∈ adaptiveTreeNodes tree,
    adaptiveConditionalVariance P (adaptiveWalshPolynomial a)
        (adaptiveTreeCell tree path) =
      adaptiveLocalWalshVariance a tree path) ∧
  (∀ a : Finset I →₀ ℝ, ∀ path ∈ adaptiveTreeNodes tree,
    adaptiveHarmonicPotential P tree (adaptiveWalshPolynomial a) path =
      adaptiveWalshPotential a tree path) ∧
  (∀ a : Finset I →₀ ℝ,
    adaptiveRootSeminormSq P tree (adaptiveWalshPolynomial a) =
      adaptiveFiniteWalshQuadraticForm tree a ∧
    0 ≤ adaptiveFiniteWalshQuadraticForm tree a) ∧
  (∀ u : (I → ℝ) → ℝ, MemLp u 2 P →
    adaptiveBoundedWalshQuadraticLimit P tree u) ∧
  adaptiveRootSeminormSq P tree g =
    adaptiveExpectedTranscriptReward P tree g ∧
  adaptiveExpectedTranscriptReward P tree g ≤ (k : ℝ)

def adaptiveNonDiagonalExample : Prop :=
  let c1 : Fin 3 := 0
  let c2 : Fin 3 := 1
  let c3 : Fin 3 := 2
  let tree : AdaptiveRevealTree (Fin 3) :=
    .query c1 (.leaf 1) (.query c2 (.leaf 1) (.leaf 1))
  legalAdaptiveTree tree ∧
    adaptiveWalshKernel tree {c3} {c1, c3} = (1 / 2 : ℝ)

def measurableAdaptiveTreeMixture [MeasurableSpace Θ]
    (M : Measure Θ) (T : Θ → AdaptiveRevealTree I) (k : ℕ) : Prop :=
  M Set.univ = 1 ∧
  (∀ θ, legalAdaptiveTree (T θ) ∧ adaptiveTreeDepth (T θ) ≤ k) ∧
  (∀ x : I → ℝ,
    AEStronglyMeasurable (fun θ => adaptiveTreeRun (T θ) x) M)

/-- Adaptive transcript Walsh-kernel theorem. -/
def adaptiveTranscriptWalshKernelTheorem : Prop :=
  ∀ {I : Type u} [Countable I] (P : Measure (I → ℝ)),
    fairIndependentRademacher P →
      ∀ {Θ : Type v} [MeasurableSpace Θ]
        (M : Measure Θ) (T : Θ → AdaptiveRevealTree I) (k : ℕ),
        measurableAdaptiveTreeMixture M T k →
          let g : (I → ℝ) → ℝ :=
            fun x => ∫ θ, adaptiveTreeRun (T θ) x ∂M
          (∃ θStar,
            adaptiveTranscriptPotentialStatement P (T θStar) k g) ∧
          adaptiveNonDiagonalExample

end
end MathlibPlus.Open.Analysis
