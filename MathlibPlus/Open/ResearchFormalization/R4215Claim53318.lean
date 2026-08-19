import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4215Family

open Filter
open scoped BigOperators Topology
noncomputable section

private abbrev Target (α : Type*) := (α → Bool) → ℝ

private noncomputable def uniformMean [Fintype (α → Bool)]
    (f : Target α) : ℝ :=
  (∑ x : α → Bool, f x) / (Fintype.card (α → Bool) : ℝ)

private noncomputable def conditionalVariance [Fintype (α → Bool)]
    [DecidableEq α] (f : Target α) (cell : Finset (α → Bool)) : ℝ :=
  let mean := (cell.sum f) / (cell.card : ℝ)
  cell.sum (fun x => (f x - mean) ^ 2) / (cell.card : ℝ)

private noncomputable def conditionalCovariance [Fintype (α → Bool)]
    [DecidableEq α] (f k : Target α) (cell : Finset (α → Bool)) : ℝ :=
  let meanF := (cell.sum f) / (cell.card : ℝ)
  let meanK := (cell.sum k) / (cell.card : ℝ)
  cell.sum (fun x => (f x - meanF) * (k x - meanK)) /
    (cell.card : ℝ)

private inductive PrefixTree (α : Type*) where
  | leaf : PrefixTree α
  | query (coordinate : α)
      (ifFalse ifTrue : PrefixTree α) : PrefixTree α

namespace PrefixTree

private def nodePaths : PrefixTree α → Finset (List Bool)
  | .leaf => {[]}
  | .query _ ifFalse ifTrue =>
      insert []
        ((nodePaths ifFalse).image (fun path => false :: path) ∪
          (nodePaths ifTrue).image (fun path => true :: path))

private def queryAt : PrefixTree α → List Bool → Option α
  | .leaf, _ => none
  | .query coordinate _ _, [] => some coordinate
  | .query _ ifFalse ifTrue, branch :: path =>
      if branch then queryAt ifTrue path else queryAt ifFalse path

private def follows : PrefixTree α → (α → Bool) → List Bool → Prop
  | _, _, [] => True
  | .leaf, _, _ :: _ => False
  | .query coordinate ifFalse ifTrue, x, branch :: path =>
      if x coordinate = branch then
        if branch then follows ifTrue x path else follows ifFalse x path
      else False

private def internalPaths (tree : PrefixTree α) : Finset (List Bool) :=
  tree.nodePaths.filter (fun path => (tree.queryAt path).isSome)

private def leafPaths (tree : PrefixTree α) : Finset (List Bool) :=
  tree.nodePaths.filter (fun path => (tree.queryAt path).isNone)

private noncomputable def transcriptCell [Fintype (α → Bool)]
    (tree : PrefixTree α) (path : List Bool) : Finset (α → Bool) :=
  let _ : DecidablePred (fun x : α → Bool => tree.follows x path) :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter (fun x => tree.follows x path)

private noncomputable def nodeProbability [Fintype (α → Bool)]
    (tree : PrefixTree α) (path : List Bool) : ℝ :=
  ((tree.transcriptCell path).card : ℝ) /
    (Fintype.card (α → Bool) : ℝ)

private noncomputable def prefixArea [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) (tree : PrefixTree α) : ℝ :=
  tree.internalPaths.sum (fun path =>
    PrefixTree.nodeProbability tree path *
      conditionalVariance f (tree.transcriptCell path))

private def queryCount : PrefixTree α → (α → Bool) → Nat
  | .leaf, _ => 0
  | .query coordinate ifFalse ifTrue, x =>
      1 + if x coordinate then queryCount ifTrue x else queryCount ifFalse x

private noncomputable def expectedLength [Fintype (α → Bool)]
    (tree : PrefixTree α) : ℝ :=
  (∑ x : α → Bool, (queryCount tree x : ℝ)) /
    (Fintype.card (α → Bool) : ℝ)

private def treePath : PrefixTree α → (α → Bool) → List Bool
  | .leaf, _ => []
  | .query coordinate ifFalse ifTrue, x =>
      if x coordinate then true :: treePath ifTrue x
      else false :: treePath ifFalse x

private def noRepeatFrom [DecidableEq α]
    (seen : Finset α) : PrefixTree α → Prop
  | .leaf => True
  | .query coordinate ifFalse ifTrue =>
      coordinate ∉ seen ∧
        noRepeatFrom (insert coordinate seen) ifFalse ∧
        noRepeatFrom (insert coordinate seen) ifTrue

private def noRepeat [DecidableEq α] (tree : PrefixTree α) : Prop :=
  noRepeatFrom ∅ tree

private def determinesOnPath [Fintype (α → Bool)]
    (f : Target α) (tree : PrefixTree α) (path : List Bool) : Prop :=
  ∀ x y, x ∈ tree.transcriptCell path → y ∈ tree.transcriptCell path →
    f x = f y

private def remainsUndetermined [Fintype (α → Bool)]
    (f : Target α) (tree : PrefixTree α) (path : List Bool) : Prop :=
  ∃ x y,
    x ∈ tree.transcriptCell path ∧ y ∈ tree.transcriptCell path ∧
      f x ≠ f y

private def firstDetermination [Fintype (α → Bool)]
    (f : Target α) (tree : PrefixTree α) : Prop :=
  (∀ path ∈ tree.internalPaths,
    remainsUndetermined f tree path) ∧
  (∀ path ∈ tree.leafPaths,
    determinesOnPath f tree path)

private def validStopped [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) (tree : PrefixTree α) : Prop :=
  noRepeat tree ∧ firstDetermination f tree

end PrefixTree

private noncomputable def intrinsicArea [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) : ℝ :=
  sInf {a : ℝ | ∃ tree : PrefixTree α,
    PrefixTree.validStopped f tree ∧ a = PrefixTree.prefixArea f tree}

private def areaOptimalPrefix [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) (tree : PrefixTree α) : Prop :=
  PrefixTree.validStopped f tree ∧
    PrefixTree.prefixArea f tree = intrinsicArea f

private def queriedAlong [DecidableEq α] : PrefixTree α → List Bool → Finset α
  | .leaf, _ => ∅
  | .query coordinate _ _, [] => {coordinate}
  | .query coordinate ifFalse ifTrue, branch :: path =>
      insert coordinate
        (if branch then queriedAlong ifTrue path else queriedAlong ifFalse path)

private noncomputable def combinedCell [Fintype (α → Bool)]
    (pre : PrefixTree α) (prefixPath : List Bool)
    (completion : PrefixTree α) (completionPath : List Bool) :
    Finset (α → Bool) :=
  let _ : DecidablePred (fun x : α → Bool =>
      pre.follows x prefixPath ∧ completion.follows x completionPath) :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter (fun x =>
    pre.follows x prefixPath ∧ completion.follows x completionPath)

private noncomputable def completionMean [Fintype (α → Bool)]
    (f : Target α) (pre : PrefixTree α) (prefixPath : List Bool)
    (completion : PrefixTree α) (completionPath : List Bool) : ℝ :=
  let cell := combinedCell pre prefixPath completion completionPath
  (cell.sum f) / (cell.card : ℝ)

private noncomputable def completionVariance [Fintype (α → Bool)]
    (f : Target α) (pre : PrefixTree α) (prefixPath : List Bool)
    (completion : PrefixTree α) (completionPath : List Bool) : ℝ :=
  let cell := combinedCell pre prefixPath completion completionPath
  (cell.sum (fun x =>
    (f x - completionMean f pre prefixPath completion completionPath) ^ 2)) /
    (cell.card : ℝ)

private noncomputable def completionAreaAt [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) (pre : PrefixTree α) (prefixPath : List Bool)
    (completion : PrefixTree α) : ℝ :=
  let preCell := pre.transcriptCell prefixPath
  completion.internalPaths.sum (fun path =>
    (((combinedCell pre prefixPath completion path).card : ℝ) /
        (preCell.card : ℝ)) *
      completionVariance f pre prefixPath completion path)

private def completionFirstDetermination [Fintype (α → Bool)]
    (f : Target α) (pre : PrefixTree α) (prefixPath : List Bool)
    (completion : PrefixTree α) : Prop :=
  (∀ path ∈ completion.internalPaths,
    ∃ x y,
      x ∈ pre.transcriptCell prefixPath ∧
      y ∈ pre.transcriptCell prefixPath ∧
      completion.follows x path ∧ completion.follows y path ∧
      f x ≠ f y) ∧
  (∀ path ∈ completion.leafPaths,
    ∀ x y,
      x ∈ pre.transcriptCell prefixPath →
      y ∈ pre.transcriptCell prefixPath →
      completion.follows x path →
      completion.follows y path →
      f x = f y)

private def completionValid [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) (pre : PrefixTree α) (prefixPath : List Bool)
    (completion : PrefixTree α) : Prop :=
  PrefixTree.noRepeatFrom (queriedAlong pre prefixPath) completion ∧
    completionFirstDetermination f pre prefixPath completion

private noncomputable def cellArea [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) (pre : PrefixTree α) (prefixPath : List Bool) : ℝ :=
  sInf {a : ℝ | ∃ completion : PrefixTree α,
    completionValid f pre prefixPath completion ∧
      a = completionAreaAt f pre prefixPath completion}

private def completionOptimal [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) (pre : PrefixTree α) (prefixPath : List Bool)
    (completion : PrefixTree α) : Prop :=
  completionValid f pre prefixPath completion ∧
    completionAreaAt f pre prefixPath completion =
      cellArea f pre prefixPath

private def graftAt : PrefixTree α → List Bool →
    (List Bool → PrefixTree α) → PrefixTree α
  | .leaf, path, completions => completions path
  | .query coordinate ifFalse ifTrue, path, completions =>
      .query coordinate
        (graftAt ifFalse (path ++ [false]) completions)
        (graftAt ifTrue (path ++ [true]) completions)

private noncomputable def forcedArea [Fintype (α → Bool)] [DecidableEq α]
    (h g : Target α) : ℝ :=
  sInf {a : ℝ | ∃ (pre : PrefixTree α)
      (completions : List Bool → PrefixTree α),
    areaOptimalPrefix h pre ∧
      (∀ path ∈ pre.leafPaths,
        completionOptimal g pre path (completions path)) ∧
      a = PrefixTree.prefixArea g
        (graftAt pre [] completions)}

private noncomputable def activePairing [Fintype (α → Bool)] [DecidableEq α]
    (f k : Target α) (tree : PrefixTree α) : ℝ :=
  tree.internalPaths.sum (fun path =>
    PrefixTree.nodeProbability tree path *
      conditionalCovariance f k (tree.transcriptCell path))

private noncomputable def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

private noncomputable def familyG (n : ℕ) : Target (Fin (n + 1)) :=
  fun x => signValue (x 0)

private noncomputable def familyH (n : ℕ) : Target (Fin (n + 1)) :=
  fun x => if (∀ i : Fin n, x i.succ = true) then 1 else -1

private noncomputable def twoZPow (exponent : ℤ) : ℝ :=
  (2 : ℝ) ^ exponent

private noncomputable def qValue (n : ℕ) : ℝ :=
  2 - twoZPow ((1 : ℤ) - (n : ℤ))

private noncomputable def hAreaValue (n : ℕ) : ℝ :=
  twoZPow ((2 : ℤ) - (n : ℤ)) *
    ((n : ℝ) - 1 + twoZPow (-(n : ℤ)))

private noncomputable def spliceGapValue (n : ℕ) (C : ℝ) : ℝ :=
  1 - twoZPow ((1 : ℤ) - (n : ℤ)) - C * hAreaValue n

/-- Claim 53318: the rare-AND/independent-literal family has the exact
area, forced-completion, active-pairing, limiting-gap, and coefficient-four
obstruction values from R-4215. -/
def claim53318_rareAndIndependentLiteralFamily : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    intrinsicArea (familyH n) = hAreaValue n ∧
      (∀ t : PrefixTree (Fin (n + 1)),
        areaOptimalPrefix (familyH n) t →
          PrefixTree.expectedLength t = qValue n) ∧
      intrinsicArea (familyG n) = 1 ∧
      forcedArea (familyH n) (familyG n) = qValue n + 1 ∧
      (∀ t : PrefixTree (Fin (n + 1)),
        areaOptimalPrefix (familyG n) t →
          activePairing (familyG n) (familyH n) t = 0) ∧
      (∀ C : ℝ, ∀ t : PrefixTree (Fin (n + 1)),
        areaOptimalPrefix (familyG n) t →
          forcedArea (familyH n) (familyG n) +
              2 * activePairing (familyG n) (familyH n) t -
              2 * intrinsicArea (familyG n) -
              C * intrinsicArea (familyH n) =
            spliceGapValue n C)) ∧
    (∀ C : ℝ,
      Filter.Tendsto (fun n : ℕ => spliceGapValue n C)
        Filter.atTop (𝓝 1)) ∧
    (∀ C : ℝ, ∃ n : ℕ, 1 ≤ n ∧ 0 < spliceGapValue n C) ∧
    (∀ n : ℕ, 1 ≤ n → n < 7 → spliceGapValue n 4 ≤ 0) ∧
    spliceGapValue 7 4 = (239 : ℝ) / 1024 ∧
    0 < spliceGapValue 7 4

end
end MathlibPlus.Open.ResearchFormalization.R4215Family
