import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoClaim61212

open scoped BigOperators
open Classical

noncomputable section

abbrev Cube := Fin 5 → Bool
abbrev History := Fin 5 → Option Bool

def rademacherSign (b : Bool) : ℝ :=
  if b then 1 else -1

def selectorOne (x : Cube) : ℝ :=
  if x 4 then -rademacherSign (x 3) else rademacherSign (x 0)

def selectorTwo (x : Cube) : ℝ :=
  if x 2 then rademacherSign (x 0) else -rademacherSign (x 3)

def selectorThree (x : Cube) : ℝ :=
  if x 1 then -rademacherSign (x 3) else rademacherSign (x 0)

def componentValue (j : Fin 3) (x : Cube) : ℝ :=
  if j.val = 0 then selectorOne x
  else if j.val = 1 then selectorTwo x
  else selectorThree x

def componentMass (_ : Fin 3) : ℝ :=
  1 / 3

def target (x : Cube) : ℝ :=
  ∑ j : Fin 3, componentMass j * componentValue j x

def explicitTarget (x : Cube) : ℝ :=
  (selectorOne x + selectorTwo x + selectorThree x) / 3

def expandedTarget (x : Cube) : ℝ :=
  (rademacherSign (x 0) + -rademacherSign (x 3)) / 2 +
    ((-rademacherSign (x 3) - rademacherSign (x 0)) / 6) *
      (rademacherSign (x 1) - rademacherSign (x 2) +
        rademacherSign (x 4))

def uniformMean (f : Cube → ℝ) : ℝ :=
  (∑ x : Cube, f x) / (Fintype.card Cube : ℝ)

def uniformVariance (f : Cube → ℝ) : ℝ :=
  (∑ x : Cube, (f x - uniformMean f) ^ 2) /
    (Fintype.card Cube : ℝ)

def emptyHistory : History :=
  fun _ => none

def consistent (h : History) (x : Cube) : Prop :=
  ∀ i : Fin 5, ∀ b : Bool, h i = some b → x i = b

noncomputable def transcriptCell (h : History) : Finset Cube :=
  Finset.univ.filter (fun x => consistent h x)

def posteriorMean (f : Cube → ℝ) (h : History) : ℝ :=
  (∑ x ∈ transcriptCell h, f x) /
    (transcriptCell h).card

def posteriorVariance (f : Cube → ℝ) (h : History) : ℝ :=
  (∑ x ∈ transcriptCell h, (f x - posteriorMean f h) ^ 2) /
    (transcriptCell h).card

def componentNonconstant (j : Fin 3) (h : History) : Prop :=
  ∃ x ∈ transcriptCell h, ∃ y ∈ transcriptCell h,
    componentValue j x ≠ componentValue j y

def targetNonconstant (h : History) : Prop :=
  ∃ x ∈ transcriptCell h, ∃ y ∈ transcriptCell h,
    target x ≠ target y

noncomputable def nonconstantComponents (h : History) : Finset (Fin 3) :=
  Finset.univ.filter (fun j => componentNonconstant j h)

def qValue (h : History) : ℝ :=
  (nonconstantComponents h).card / 3

noncomputable def candidatePotential (h : History) : ℝ :=
  if targetNonconstant h then 2 * qValue h ^ 2 else 0

def observe (h : History) (i : Fin 5) (b : Bool) : History :=
  Function.update h i (some b)

noncomputable def freshCoordinates (h : History) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => h i = none)

inductive QueryTree where
  | leaf (value : ℝ)
  | query (coordinate : Fin 5) (ifFalse ifTrue : QueryTree)

namespace QueryTree

def evaluate : QueryTree → Cube → ℝ
  | .leaf value, _ => value
  | .query coordinate ifFalse ifTrue, x =>
      if x coordinate then evaluate ifTrue x else evaluate ifFalse x

def depth : QueryTree → ℕ
  | .leaf _ => 0
  | .query _ ifFalse ifTrue => 1 + max (depth ifFalse) (depth ifTrue)

def paths : QueryTree → Finset (List Bool)
  | .leaf _ => {[]}
  | .query _ ifFalse ifTrue =>
      insert []
        ((paths ifFalse).image (fun p => false :: p) ∪
          (paths ifTrue).image (fun p => true :: p))

def queryAt : QueryTree → List Bool → Option (Fin 5)
  | .leaf _, _ => none
  | .query coordinate _ _, [] => some coordinate
  | .query _ ifFalse ifTrue, branch :: path =>
      if branch then queryAt ifTrue path else queryAt ifFalse path

def internalPaths (tree : QueryTree) : Finset (List Bool) :=
  (paths tree).filter (fun path => (queryAt tree path).isSome)

def terminalPaths (tree : QueryTree) : Finset (List Bool) :=
  (paths tree).filter (fun path => (queryAt tree path).isNone)

def pathHistory : QueryTree → List Bool → History
  | .leaf _, _ => emptyHistory
  | .query _ _ _, [] => emptyHistory
  | .query coordinate ifFalse ifTrue, branch :: path =>
      Function.update
        (pathHistory (if branch then ifTrue else ifFalse) path)
        coordinate (some branch)

def noRepeatFrom (seen : Finset (Fin 5)) : QueryTree → Prop
  | .leaf _ => True
  | .query coordinate ifFalse ifTrue =>
      coordinate ∉ seen ∧
        noRepeatFrom (insert coordinate seen) ifFalse ∧
        noRepeatFrom (insert coordinate seen) ifTrue

def noRepeat (tree : QueryTree) : Prop :=
  noRepeatFrom ∅ tree

end QueryTree

open QueryTree

def computesComponent (j : Fin 3) (tree : QueryTree) : Prop :=
  ∀ x : Cube, tree.evaluate x = componentValue j x

def terminalComponentMeasurable (j : Fin 3) (tree : QueryTree) : Prop :=
  ∀ path ∈ tree.terminalPaths,
    ¬ componentNonconstant j (tree.pathHistory path)

def validComponentBlock (j : Fin 3) (tree : QueryTree) : Prop :=
  tree.noRepeat ∧
    tree.depth = 2 ∧
    computesComponent j tree ∧
    terminalComponentMeasurable j tree

def readTree (i : Fin 5) : QueryTree :=
  .query i (.leaf (-1)) (.leaf 1)

def negReadTree (i : Fin 5) : QueryTree :=
  .query i (.leaf 1) (.leaf (-1))

def componentTree (j : Fin 3) : QueryTree :=
  if j.val = 0 then
    .query 4 (readTree 0) (negReadTree 3)
  else if j.val = 1 then
    .query 2 (negReadTree 3) (readTree 0)
  else
    .query 1 (readTree 0) (negReadTree 3)

def pathProbability (tree : QueryTree) (path : List Bool) : ℝ :=
  (transcriptCell (tree.pathHistory path)).card /
    (Fintype.card Cube : ℝ)

noncomputable def prequeryVarianceArea (tree : QueryTree) : ℝ :=
  ∑ path ∈ tree.internalPaths,
    pathProbability tree path *
      posteriorVariance target (tree.pathHistory path)

noncomputable def terminalPotentialExpectation (tree : QueryTree) : ℝ :=
  ∑ path ∈ tree.terminalPaths,
    pathProbability tree path *
      candidatePotential (tree.pathHistory path)

def blockCharge (tree : QueryTree) : ℝ :=
  prequeryVarianceArea tree + terminalPotentialExpectation tree

def componentDistribution (p : Fin 3 → ℝ) : Prop :=
  (∀ j : Fin 3, 0 ≤ p j) ∧ (∑ j : Fin 3, p j) = 1

def expectedCanonicalBlockCharge (p : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3, p j * blockCharge (componentTree j)

def randomizedPeelingFails : Prop :=
  ∀ p : Fin 3 → ℝ,
    componentDistribution p →
      expectedCanonicalBlockCharge p > candidatePotential emptyHistory

noncomputable def bellmanArea : ℕ → History → ℝ
  | 0, h => if targetNonconstant h then posteriorVariance target h else 0
  | n + 1, h =>
      if targetNonconstant h then
        posteriorVariance target h +
          sInf {v : ℝ |
            ∃ i : Fin 5, i ∈ freshCoordinates h ∧
              v = (bellmanArea n (observe h i false) +
                bellmanArea n (observe h i true)) / 2}
      else 0

def bellmanOptimalRootArea : ℝ :=
  bellmanArea 5 emptyHistory

/-- The concrete five-sign law, all three genuine depth-two component blocks,
the exact `20/9` charge against `U(empty)=2`, the randomized-component
obstruction, and the exact Bellman value from Claim 61212. -/
def claim61212_depthTwoSquaredNonconstantMassObstruction : Prop :=
  Fintype.card Cube = 32 ∧
  (∀ j : Fin 3, componentMass j = 1 / 3) ∧
  (∀ x : Cube, target x = explicitTarget x) ∧
  (∀ x : Cube, target x = expandedTarget x) ∧
  uniformVariance target = 2 / 3 ∧
  (∀ j : Fin 3, validComponentBlock j (componentTree j)) ∧
  (∀ j : Fin 3, ∀ tree : QueryTree,
    validComponentBlock j tree → blockCharge tree = 20 / 9) ∧
  candidatePotential emptyHistory = 2 ∧
  (∀ j : Fin 3, ∀ tree : QueryTree,
    validComponentBlock j tree → blockCharge tree > 2) ∧
  randomizedPeelingFails ∧
  bellmanOptimalRootArea = 17 / 12 ∧
  bellmanOptimalRootArea < 2

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaDepthTwoClaim61212
