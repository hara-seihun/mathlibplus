import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R3867

noncomputable section

/-- A finite unbiased Rademacher assignment. -/
abbrev RademacherAssignment (n : ℕ) := Fin n → Bool

/-- A posterior state records the coordinates already revealed. -/
abbrev PartialAssignment (n : ℕ) := Fin n → Option Bool

/-- A fixed-global-level Boolean decision tree. -/
inductive LevelTree (n : ℕ) where
  | leaf (value : ℝ) : LevelTree n
  | query (coordinate : Fin n) (level : ℕ)
      (whenFalse whenTrue : LevelTree n) : LevelTree n

/-- Evaluation of a displayed tree. -/
def LevelTree.evaluate {n : ℕ} :
    LevelTree n → RademacherAssignment n → ℝ
  | .leaf value, _ => value
  | .query coordinate _ whenFalse whenTrue, x =>
      if x coordinate then whenTrue.evaluate x else whenFalse.evaluate x

/-- The displayed coordinate/level path under a completion. -/
def LevelTree.queryPath {n : ℕ} :
    LevelTree n → RademacherAssignment n → List (Fin n × ℕ)
  | .leaf _, _ => []
  | .query coordinate level whenFalse whenTrue, x =>
      (coordinate, level) ::
        if x coordinate then whenTrue.queryPath x else whenFalse.queryPath x

/-- Consistency of a full completion with a posterior state. -/
def consistent {n : ℕ} (h : PartialAssignment n)
    (x : RademacherAssignment n) : Prop :=
  ∀ i b, h i = some b → x i = b

/-- All unbiased completions of a posterior state. -/
noncomputable def completions {n : ℕ} (h : PartialAssignment n) :
    Finset (RademacherAssignment n) :=
  Finset.univ.filter
    (fun x => @decide (consistent h x) (Classical.propDecidable _))

/-- Reveal one oracle coordinate. -/
def partialUpdate {n : ℕ} (h : PartialAssignment n)
    (i : Fin n) (b : Bool) : PartialAssignment n :=
  Function.update h i (some b)

/-- Conditional posterior mean on a finite completion fibre. -/
def conditionalAverage {n : ℕ} (h : PartialAssignment n)
    (f : RademacherAssignment n → ℝ) : ℝ :=
  (completions h).sum f / ((completions h).card : ℝ)

/-- Conditional posterior variance on a finite completion fibre. -/
def conditionalVariance {n : ℕ} (h : PartialAssignment n)
    (f : RademacherAssignment n → ℝ) : ℝ :=
  let mean := conditionalAverage h f
  conditionalAverage h (fun x => (f x - mean) ^ 2)

/-- The deepest unresolved coordinate on a sampled displayed path.  The
specific trees below have strictly increasing displayed levels along every
path, so the last unresolved path entry is the greatest-level entry. -/
def deepestUnresolved {n : ℕ} (h : PartialAssignment n)
    (tree : LevelTree n) (x : RademacherAssignment n) : Option (Fin n) :=
  ((tree.queryPath x).filter (fun q => (h q.1).isNone)).getLast?.map Prod.fst

/-- The four-coordinate first fixed-level component. -/
def firstFourTree : LevelTree 4 :=
  .query (1 : Fin 4) 1
    (.query (0 : Fin 4) 2 (.leaf (-1 : ℝ)) (.leaf 1))
    (.query (3 : Fin 4) 2 (.leaf (-1 : ℝ)) (.leaf 1))

/-- The four-coordinate second fixed-level component. -/
def secondFourTree : LevelTree 4 :=
  .query (2 : Fin 4) 1
    (.query (0 : Fin 4) 2 (.leaf (-1 : ℝ)) (.leaf 1))
    (.query (3 : Fin 4) 2 (.leaf (-1 : ℝ)) (.leaf 1))

/-- The two component masses in the R-3867 witness. -/
def fourComponentWeight (c : Fin 2) : ℝ :=
  if c = 0 then (25 : ℝ) / 27 else (2 : ℝ) / 27

/-- The displayed component selected by a component sample. -/
def fourComponentTree (c : Fin 2) : LevelTree 4 :=
  if c = 0 then firstFourTree else secondFourTree

/-- The posterior target, namely the mixture mean of the two displayed
Boolean components. -/
def fourTarget (x : RademacherAssignment 4) : ℝ :=
  ∑ c : Fin 2, fourComponentWeight c *
    (fourComponentTree c).evaluate x

/-- Unnormalised action mass from sampling a component and an independent
uniform posterior completion. -/
def fourActionMass (h : PartialAssignment 4) (i : Fin 4) : ℝ :=
  ∑ c : Fin 2,
    fourComponentWeight c *
      ((completions h).filter
        (fun x =>
          deepestUnresolved h (fourComponentTree c) x = some i)).card /
      (completions h).card

/-- The mass of component/completion samples having a queryable path. -/
def fourActiveMass (h : PartialAssignment 4) : ℝ :=
  ∑ i : Fin 4, fourActionMass h i

/-- The action distribution after resampling samples whose path has no
unresolved coordinate. -/
def fourActionProbability (h : PartialAssignment 4) (i : Fin 4) : ℝ :=
  if fourActiveMass h = 0 then 0 else fourActionMass h i / fourActiveMass h

/-- Exact finite recurrence for the sampled-component/deepest-unresolved
policy on the four-coordinate witness. -/
def fourPolicyAreaAux : ℕ → PartialAssignment 4 → ℝ
  | 0, _ => 0
  | k + 1, h =>
      if conditionalVariance h fourTarget = 0 then 0 else
        conditionalVariance h fourTarget +
          ∑ i : Fin 4, fourActionProbability h i *
            (fourPolicyAreaAux k (partialUpdate h i false) +
              fourPolicyAreaAux k (partialUpdate h i true)) / 2

/-- The root-inclusive area of the stated fixed-level policy. -/
def fourPolicyArea (h : PartialAssignment 4) : ℝ :=
  fourPolicyAreaAux 4 h

/-- The empty posterior state. -/
def emptyPartialAssignment {n : ℕ} : PartialAssignment n :=
  fun _ => none

/-- Claim 51653: the displayed tree mixture, its posterior-sampled
deepest-unresolved action law, exact Bellman-style recurrence, and the exact
policy obstruction are retained.  No unrestricted optimum is asserted. -/
def claim51653 : Prop :=
  (∀ h : PartialAssignment 4,
      conditionalVariance h fourTarget = 0 → fourPolicyArea h = 0) ∧
    (∀ h : PartialAssignment 4,
      conditionalVariance h fourTarget ≠ 0 →
        fourPolicyArea h = conditionalVariance h fourTarget +
          ∑ i : Fin 4, fourActionProbability h i *
            (fourPolicyArea (partialUpdate h i false) +
              fourPolicyArea (partialUpdate h i true)) / 2) ∧
    fourComponentWeight (0 : Fin 2) = (25 : ℝ) / 27 ∧
    fourComponentWeight (1 : Fin 2) = (2 : ℝ) / 27 ∧
    fourComponentWeight (0 : Fin 2) + fourComponentWeight (1 : Fin 2) = 1 ∧
    fourPolicyArea (emptyPartialAssignment : PartialAssignment 4) =
      (6161 : ℝ) / 2916 ∧
    (6161 : ℝ) / 2916 = 2 + (317 : ℝ) / 2916 ∧
    2 < (6161 : ℝ) / 2916

/-- The shared-leaf component with `X_i` at level one and `Y` at level two.
Its leaves evaluate to the product `X_i Y` under the Boolean sign convention. -/
def sharedLeafTree (m : ℕ) (i : Fin m) : LevelTree (m + 1) :=
  .query (Fin.castSucc i) 1
    (.query (Fin.last m) 2 (.leaf (1 : ℝ)) (.leaf (-1)))
    (.query (Fin.last m) 2 (.leaf (-1 : ℝ)) (.leaf 1))

/-- The sign value of a Boolean Rademacher coordinate. -/
def rademacherSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Uniform averaging on a finite Rademacher cube. -/
def uniformAverage {n : ℕ} (f : RademacherAssignment n → ℝ) : ℝ :=
  (∑ x : RademacherAssignment n, f x) /
    (Fintype.card (RademacherAssignment n) : ℝ)

/-- The shared-leaf target `g_m = Y m⁻¹ ∑ X_i`. -/
def sharedLeafTarget (m : ℕ)
    (x : RademacherAssignment (m + 1)) : ℝ :=
  rademacherSign (x (Fin.last m)) *
    (∑ i : Fin m, rademacherSign (x (Fin.castSucc i))) / (m : ℝ)

/-- The displayed shared-leaf paths. -/
def sharedLeafPathOrder (m : ℕ) : Prop :=
  ∀ (i : Fin m) (x : RademacherAssignment (m + 1)),
    (sharedLeafTree m i).queryPath x =
      [(Fin.castSucc i, 1), (Fin.last m, 2)]

/-- The corrected conjunction of the two action-order implications: while `Y`
is unknown it is deepest, and once `Y` is known an unresolved `X_i` is next. -/
def sharedLeafActionOrder (m : ℕ) : Prop :=
  ∀ (h : PartialAssignment (m + 1)) (i : Fin m)
    (x : RademacherAssignment (m + 1)),
    (h (Fin.last m) = none →
      deepestUnresolved h (sharedLeafTree m i) x = some (Fin.last m)) ∧
    (h (Fin.last m) ≠ none →
      h (Fin.castSucc i) = none →
        deepestUnresolved h (sharedLeafTree m i) x = some (Fin.castSucc i))

/-- Equal component weights for the shared-leaf family. -/
def sharedComponentWeight (m : ℕ) (_i : Fin m) : ℝ :=
  1 / (m : ℝ)

/-- Action mass for the same sampled-component/deepest-unresolved policy. -/
def sharedActionMass (m : ℕ) (h : PartialAssignment (m + 1))
    (i : Fin (m + 1)) : ℝ :=
  ∑ j : Fin m,
    sharedComponentWeight m j *
      ((completions h).filter
        (fun x =>
          deepestUnresolved h (sharedLeafTree m j) x = some i)).card /
      (completions h).card

/-- Total queryable mass and the resampled action distribution. -/
def sharedActiveMass (m : ℕ) (h : PartialAssignment (m + 1)) : ℝ :=
  ∑ i : Fin (m + 1), sharedActionMass m h i

/-- The shared-leaf action distribution. -/
def sharedActionProbability (m : ℕ) (h : PartialAssignment (m + 1))
    (i : Fin (m + 1)) : ℝ :=
  if sharedActiveMass m h = 0 then 0 else
    sharedActionMass m h i / sharedActiveMass m h

/-- Finite recurrence for the stated sampled-path policy on `g_m`. -/
def sharedPolicyAreaAux (m : ℕ)
    (f : RademacherAssignment (m + 1) → ℝ) :
    ℕ → PartialAssignment (m + 1) → ℝ
  | 0, _ => 0
  | k + 1, h =>
      if conditionalVariance h f = 0 then 0 else
        conditionalVariance h f +
          ∑ i : Fin (m + 1), sharedActionProbability m h i *
            (sharedPolicyAreaAux m f k (partialUpdate h i false) +
              sharedPolicyAreaAux m f k (partialUpdate h i true)) / 2

/-- The root-inclusive shared-leaf policy area and the comparison potential. -/
def sharedLeafArea (m : ℕ) : ℝ :=
  sharedPolicyAreaAux m (sharedLeafTarget m) (m + 1)
    (emptyPartialAssignment : PartialAssignment (m + 1))

/-- The level-two rank packet after the level-one selector completion. -/
def sharedLeafRankPacket (m : ℕ)
    (x : RademacherAssignment m) : Fin 2 → ℝ :=
  fun _ => (∑ i : Fin m, rademacherSign (x i)) / (m : ℝ)

/-- The squared rank-packet potential, with the two coordinates of the
level-two packet retained explicitly. -/
def sharedLeafRankPotential (m : ℕ) : ℝ :=
  2 * uniformAverage (fun x : RademacherAssignment m =>
    (sharedLeafRankPacket m x (0 : Fin 2)) ^ 2)

/-- Claim 51654: exact Y-then-X action behavior, area, comparison potential,
ratio, and the exact replay range. -/
def claim51654 : Prop :=
  (∀ m : ℕ, 0 < m →
      sharedLeafPathOrder m ∧
      sharedLeafActionOrder m ∧
      sharedLeafArea m = ((m : ℝ) + 3) / (2 * (m : ℝ)) ∧
      sharedLeafRankPotential m = 2 / (m : ℝ) ∧
      sharedLeafArea m / sharedLeafRankPotential m =
        ((m : ℝ) + 3) / 4) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ 6 →
      sharedLeafArea m = ((m : ℝ) + 3) / (2 * (m : ℝ)))

end

end MathlibPlus.Open.ResearchFormalization.R3867
