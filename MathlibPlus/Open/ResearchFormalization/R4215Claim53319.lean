import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

namespace R4215

abbrev Target (α : Type*) := (α → Bool) → ℝ

private noncomputable def uniformMean [Fintype (α → Bool)] (f : Target α) : ℝ :=
  (∑ x : α → Bool, f x) / (Fintype.card (α → Bool) : ℝ)

private noncomputable def targetVariance [Fintype (α → Bool)] (f : Target α) : ℝ :=
  (∑ x : α → Bool, (f x - uniformMean f) ^ 2) /
    (Fintype.card (α → Bool) : ℝ)

private noncomputable def targetCovariance [Fintype (α → Bool)] (f k : Target α) : ℝ :=
  (∑ x : α → Bool,
      (f x - uniformMean f) * (k x - uniformMean k)) /
    (Fintype.card (α → Bool) : ℝ)

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

private noncomputable def conditionalMean [Fintype (α → Bool)]
    (f : Target α) (cell : Finset (α → Bool)) : ℝ :=
  (cell.sum f) / (cell.card : ℝ)

private noncomputable def conditionalVariance [Fintype (α → Bool)]
    [DecidableEq α] (f : Target α) (cell : Finset (α → Bool)) : ℝ :=
  (cell.sum (fun x => (f x - conditionalMean f cell) ^ 2)) /
    (cell.card : ℝ)

private noncomputable def conditionalCovariance [Fintype (α → Bool)]
    [DecidableEq α] (f k : Target α) (cell : Finset (α → Bool)) : ℝ :=
  (cell.sum (fun x =>
      (f x - conditionalMean f cell) *
        (k x - conditionalMean k cell))) /
    (cell.card : ℝ)

private noncomputable def prefixArea [Fintype (α → Bool)] [DecidableEq α]
    (f : Target α) (tree : PrefixTree α) : ℝ :=
  tree.internalPaths.sum (fun path =>
    PrefixTree.nodeProbability tree path *
      PrefixTree.conditionalVariance f (tree.transcriptCell path))

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

private def determinesPrefix (f : Target α) (tree : PrefixTree α) : Prop :=
  ∀ x y, tree.treePath x = tree.treePath y → f x = f y

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

private def completionDetermines [Fintype (α → Bool)]
    (f : Target α) (pre : PrefixTree α) (prefixPath : List Bool)
    (completion : PrefixTree α) : Prop :=
  ∀ x y,
    x ∈ pre.transcriptCell prefixPath →
    y ∈ pre.transcriptCell prefixPath →
    completion.treePath x = completion.treePath y →
    f x = f y

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
      PrefixTree.conditionalCovariance f k (tree.transcriptCell path))

private def rootCoordinate : PrefixTree α → Option α
  | .leaf => none
  | .query coordinate _ _ => some coordinate

private def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

private def r4215G : Target (Fin 8) :=
  fun x => signValue (x 0)

private def r4215H : Target (Fin 8) :=
  fun x => if (∀ i : Fin 7, x i.succ = true) then 1 else -1

/-- Claim 53319: the exact eight-coordinate coefficient-four splice obstruction
for an independent literal and the seven-coordinate rare AND. -/
def claim53319 : Prop :=
  intrinsicArea r4215G = 1 ∧
    intrinsicArea r4215H = (769 : ℝ) / 4096 ∧
    (∀ t : PrefixTree (Fin 8),
      areaOptimalPrefix r4215H t →
        PrefixTree.expectedLength t = (127 : ℝ) / 64) ∧
    forcedArea r4215H r4215G = (191 : ℝ) / 64 ∧
    (∀ t : PrefixTree (Fin 8),
      areaOptimalPrefix r4215G t →
        rootCoordinate t = some (0 : Fin 8)) ∧
    (∀ t : PrefixTree (Fin 8),
      areaOptimalPrefix r4215G t →
        activePairing r4215G r4215H t = 0) ∧
    (∀ t : PrefixTree (Fin 8),
      areaOptimalPrefix r4215G t →
        forcedArea r4215H r4215G +
              2 * activePairing r4215G r4215H t -
              2 * intrinsicArea r4215G -
              4 * intrinsicArea r4215H = (239 : ℝ) / 1024 ∧
          0 < forcedArea r4215H r4215G +
              2 * activePairing r4215G r4215H t -
              2 * intrinsicArea r4215G -
              4 * intrinsicArea r4215H ∧
          ¬ (forcedArea r4215H r4215G +
              2 * activePairing r4215G r4215H t ≤
            2 * intrinsicArea r4215G + 4 * intrinsicArea r4215H))

end R4215

end MathlibPlus.Open.ResearchFormalization
