import MathlibPlus.Open.Analysis.AdaptiveTranscriptWalshKernel

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaCommonRootDepth2Claim61109

noncomputable section

open Classical
open MathlibPlus.Open.Analysis

abbrev Coordinate (I : Type*) := Option I
abbrev Oracle (I : Type*) := Coordinate I → ℝ
abbrev RevealTranscript (I : Type*) := List (Coordinate I × ℝ)
abbrev RevealPolicy (I : Type*) := RevealTranscript I → Option (Coordinate I)

/-- The two allowed leaf signs. -/
def signedLeafValue (c : ℝ) : Prop :=
  c = -1 ∨ c = 1

/-- A branch either stops at a sign or queries one branch coordinate and
returns `d X_i` with `d` a sign. -/
def branchShape {I : Type*} :
    AdaptiveRevealTree (Coordinate I) → Prop
  | .leaf c => signedLeafValue c
  | .query (some _) (.leaf negative) (.leaf positive) =>
      ∃ d : ℝ, signedLeafValue d ∧
        negative = -d ∧ positive = d
  | _ => False

/-- The exact common-root depth-two component class: constants are allowed,
and every nonconstant component has the root coordinate `none` first. -/
def commonRootComponent {I : Type*}
    (tree : AdaptiveRevealTree (Coordinate I)) : Prop :=
  legalAdaptiveTree tree ∧
    adaptiveTreeDepth tree ≤ 2 ∧
      ((∃ c : ℝ, tree = .leaf c ∧ signedLeafValue c) ∨
        ∃ negative positive : AdaptiveRevealTree (Coordinate I),
          tree = .query none negative positive ∧
            branchShape negative ∧ branchShape positive)

/-- The coordinate and sign supplied by a nonconstant branch, when the tree
has the displayed common-root shape. -/
def branchData {I : Type*}
    (tree : AdaptiveRevealTree (Coordinate I)) (s : Bool) :
    Option (I × ℝ) :=
  match tree with
  | .query none negative positive =>
      match (if s then positive else negative) with
      | .query (some i) _ (.leaf d) => some (i, d)
      | _ => none
  | _ => none

def branchCoordinate {I : Type*}
    (tree : AdaptiveRevealTree (Coordinate I)) (s : Bool) : Option I :=
  (branchData tree s).map Prod.fst

def branchSign {I : Type*}
    (tree : AdaptiveRevealTree (Coordinate I)) (s : Bool) : ℝ :=
  match branchData tree s with
  | none => 0
  | some data => data.2

/-- The aggregate coefficient of branch coordinate `i` after the root has
value `s`. -/
def aggregateCoefficient {I J : Type*} [Countable J]
    (weights : J → ℝ) (trees : J → AdaptiveRevealTree (Coordinate I))
    (s : Bool) (i : I) : ℝ :=
  ∑' j : J,
    if branchCoordinate (trees j) s = some i then
      weights j * branchSign (trees j) s
    else 0

/-- The fixed target mixture in the exact countable component carrier. -/
def mixtureTarget {I J : Type*} [Countable J]
    (weights : J → ℝ) (trees : J → AdaptiveRevealTree (Coordinate I)) :
    Oracle I → ℝ :=
  fun O => ∑' j : J, weights j * adaptiveTreeRun (trees j) O

/-- Nonnegative weights with explicit real summability and total mass. -/
def massCondition {J : Type*} [Countable J]
    (weights : J → ℝ) (S : ℝ) : Prop :=
  (∀ j, 0 ≤ weights j) ∧
    Summable weights ∧
      (∑' j, weights j) = S ∧ S ≤ 1

def recordedValue {I : Type*}
    (h : RevealTranscript I) (c : Coordinate I) : Option ℝ :=
  (h.find? (fun pair => pair.1 = c)).map Prod.snd

def transcriptCompatible {I : Type*}
    (h : RevealTranscript I) (O : Oracle I) : Prop :=
  ∀ pair ∈ h, O pair.1 = pair.2

def transcriptCell {I : Type*}
    (h : RevealTranscript I) : Set (Oracle I) :=
  {O | transcriptCompatible h O}

def transcriptStep {I : Type*}
    (h : RevealTranscript I) (O : Oracle I)
    (action : Option (Coordinate I)) : RevealTranscript I :=
  match action with
  | none => h
  | some c => h ++ [(c, O c)]

def historyAt {I : Type*}
    (π : RevealPolicy I) (O : Oracle I) : ℕ → RevealTranscript I
  | 0 => []
  | n + 1 =>
      let h := historyAt π O n
      transcriptStep h O (π h)

/-- A legal policy never queries a coordinate already present in its
transcript; `none` is the distinguished root coordinate, not stopping. -/
def legalRevealPolicy {I : Type*} (π : RevealPolicy I) : Prop :=
  ∀ h c, π h = some c → recordedValue h c = none

def rootFirst {I : Type*} (π : RevealPolicy I) : Prop :=
  π [] = some none

def branchCount {I : Type*} (h : RevealTranscript I) : ℕ :=
  (h.filter (fun pair => pair.1 ≠ none)).length

def rootBranch (s : ℝ) : Bool :=
  s = 1

/-- The prescribed policy: reveal the root first, then follow the branch
schedule according to the root sign and the number of branch reveals already
recorded. -/
def scheduledPolicy {I : Type*}
    (order : Bool → ℕ → Option I) : RevealPolicy I :=
  fun h =>
    match recordedValue h none with
    | none => some none
    | some s =>
        match order (rootBranch s) (branchCount h) with
        | none => none
        | some i => some (some i)

def policyPosteriorVariance {I : Type*}
    (P : Measure (Oracle I)) (π : RevealPolicy I)
    (μ : Oracle I → ℝ) (O : Oracle I) (m : ℕ) : ℝ :=
  adaptiveConditionalVariance P μ
    (transcriptCell (historyAt π O m))

/-- Root-inclusive cumulative posterior-variance area. -/
def policyArea {I : Type*}
    (P : Measure (Oracle I)) (π : RevealPolicy I)
    (μ : Oracle I → ℝ) : ℝ :=
  ∑' m : ℕ, ∫ O,
    policyPosteriorVariance P π μ O m ∂P

/-- The branch schedule enumerates exactly the nonzero aggregate coefficients,
without repetition, in nonincreasing absolute value. -/
def branchScheduleCondition {I J : Type*} [Countable J]
    (weights : J → ℝ) (trees : J → AdaptiveRevealTree (Coordinate I))
    (order : Bool → ℕ → Option I) : Prop :=
  ∀ s : Bool,
    (∀ m i, order s m = some i →
      aggregateCoefficient weights trees s i ≠ 0) ∧
      (∀ i, aggregateCoefficient weights trees s i ≠ 0 →
        ∃ m, order s m = some i) ∧
        (∀ m n i k, m < n →
          order s m = some i → order s n = some k →
            |aggregateCoefficient weights trees s i| ≥
              |aggregateCoefficient weights trees s k|) ∧
          (∀ m n, m ≤ n → order s m = none → order s n = none) ∧
            (∀ m n i, m < n → order s m = some i →
              order s n ≠ some i)

def finitelyDetermines {I : Type*}
    (π : RevealPolicy I) (μ : Oracle I → ℝ) : Prop :=
  ∀ O, ∃ m,
    π (historyAt π O m) = none ∧
      ∀ O', transcriptCompatible (historyAt π O m) O' →
        μ O' = μ O

def completedLimitDetermines {I : Type*}
    (P : Measure (Oracle I)) (π : RevealPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  ∀ O,
    Filter.Tendsto
      (fun m => policyPosteriorVariance P π μ O m)
      Filter.atTop (nhds 0)

def finiteOrCompletedLimitDetermines {I : Type*}
    (P : Measure (Oracle I)) (π : RevealPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  finitelyDetermines π μ ∨ completedLimitDetermines P π μ

/-- The corrected sharpness component `X₀ X₁`: the negative root branch is
`-X₁`, while the positive root branch is `X₁`. -/
def sharpComponentTree : AdaptiveRevealTree (Coordinate Unit) :=
  .query none
    (.query (some ()) (.leaf 1) (.leaf (-1)))
    (.query (some ()) (.leaf (-1)) (.leaf 1))

def sharpWeights : Unit → ℝ :=
  fun _ => 1

def sharpTrees : Unit → AdaptiveRevealTree (Coordinate Unit) :=
  fun _ => sharpComponentTree

def sharpTarget : Oracle Unit → ℝ :=
  mixtureTarget sharpWeights sharpTrees

def sharpTargetProduct : Oracle Unit → ℝ :=
  fun O => O none * O (some ())

def sharpOrder : Bool → ℕ → Option Unit :=
  fun _ m => if m = 0 then some () else none

def sharpPolicy : RevealPolicy Unit :=
  scheduledPolicy sharpOrder

def sharpMass : Prop :=
  massCondition sharpWeights 1

/-- The sharpness part of Claim 61109, including the explicit one-component
product witness and the lower bound for every legal determining policy. -/
def sharpnessClaim : Prop :=
  ∃ P : Measure (Oracle Unit),
    fairIndependentRademacher P ∧
      sharpMass ∧
        (∀ O,
          (O none = -1 ∨ O none = 1) →
            (O (some ()) = -1 ∨ O (some ()) = 1) →
              sharpTarget O = sharpTargetProduct O) ∧
          legalRevealPolicy sharpPolicy ∧
            finiteOrCompletedLimitDetermines P sharpPolicy sharpTarget ∧
              policyArea P sharpPolicy sharpTarget = 2 ∧
                (∀ π : RevealPolicy Unit,
                  legalRevealPolicy π →
                    finiteOrCompletedLimitDetermines P π sharpTarget →
                      2 ≤ policyArea P π sharpTarget)

/-- Claim 61109: a common first Rademacher root reduces every branch to a
weighted affine coordinate mixture, whose ordered adaptive reveal policy has
root-inclusive area at most `2 S² ≤ 2`; the coefficient is sharp. -/
def claim61109 : Prop :=
  (∀ {I J : Type*} [Countable I] [Countable J]
      (P : Measure (Oracle I)) (S : ℝ)
      (weights : J → ℝ)
      (trees : J → AdaptiveRevealTree (Coordinate I)),
      fairIndependentRademacher P →
        massCondition weights S →
          (∀ j, commonRootComponent (trees j)) →
            let M := mixtureTarget weights trees
            ∃ order : Bool → ℕ → Option I,
              branchScheduleCondition weights trees order ∧
                let π := scheduledPolicy order
                rootFirst π ∧
                  legalRevealPolicy π ∧
                    finiteOrCompletedLimitDetermines P π M ∧
                      policyArea P π M ≤ 2 * S ^ 2 ∧
                        2 * S ^ 2 ≤ 2) ∧
    sharpnessClaim

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaCommonRootDepth2Claim61109
