import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaBlockPotential61311

noncomputable section

abbrev RademacherSign := Bool
abbrev Cube (n : ℕ) := Fin n → RademacherSign
abbrev PartialAssignment (n : ℕ) := Fin n → Option RademacherSign
abbrev BooleanTable (n : ℕ) := Cube n → RademacherSign

/-- The numerical value of a Rademacher sign. -/
def signValue : RademacherSign → ℝ
  | false => -1
  | true => 1

/-- A deterministic binary decision tree for a Boolean table. -/
inductive BooleanTree (n : ℕ) where
  | leaf (value : RademacherSign)
  | query (coordinate : Fin n)
      (negative positive : BooleanTree n)

namespace BooleanTree

def evaluate : BooleanTree n → Cube n → RademacherSign
  | .leaf value, _ => value
  | .query coordinate negative positive, x =>
      if x coordinate then evaluate positive x else evaluate negative x

def depth : BooleanTree n → ℕ
  | .leaf _ => 0
  | .query _ negative positive => 1 + max (depth negative) (depth positive)

def support : BooleanTree n → Finset (Fin n)
  | .leaf _ => ∅
  | .query coordinate negative positive =>
      insert coordinate (support negative ∪ support positive)

/-- No root-to-leaf path reveals a coordinate twice. -/
def noRepeat : BooleanTree n → Prop
  | .leaf _ => True
  | .query coordinate negative positive =>
      coordinate ∉ support negative ∧
        coordinate ∉ support positive ∧
        noRepeat negative ∧ noRepeat positive

end BooleanTree

/-- A table is computed by a tree on every point of the cube. -/
def treeComputes (tree : BooleanTree n) (table : BooleanTable n) : Prop :=
  ∀ x, tree.evaluate x = table x

/-- The minimum worst-case depth among deterministic fresh-query trees. -/
noncomputable def tableDepth (table : BooleanTable n) : ℕ :=
  sInf {d : ℕ |
    ∃ tree : BooleanTree n,
      tree.noRepeat ∧ treeComputes tree table ∧ tree.depth = d}

def compatible (h : PartialAssignment n) (x : Cube n) : Prop :=
  ∀ i, match h i with
    | none => True
    | some value => x i = value

noncomputable def cell (h : PartialAssignment n) : Finset (Cube n) :=
  Finset.univ.filter (fun x => compatible h x)

def updateAssignment (h : PartialAssignment n) (i : Fin n)
    (value : RademacherSign) : PartialAssignment n :=
  Function.update h i (some value)

def treeFresh (h : PartialAssignment n) (tree : BooleanTree n) : Prop :=
  tree.noRepeat ∧ ∀ i ∈ tree.support, h i = none

/-- Computation of a restricted table on the current transcript cell. -/
def restrictedTreeComputes (h : PartialAssignment n)
    (tree : BooleanTree n) (table : BooleanTable n) : Prop :=
  ∀ x, compatible h x → tree.evaluate x = table x

/-- A minimum-depth tree for the table after the coordinates in `h` are fixed. -/
def minimumRestrictedTree (h : PartialAssignment n)
    (table : BooleanTable n) (tree : BooleanTree n) : Prop :=
  treeFresh h tree ∧
    restrictedTreeComputes h tree table ∧
    ∀ other : BooleanTree n,
      treeFresh h other →
        restrictedTreeComputes h other table →
          tree.depth ≤ other.depth

/-- Uniform mean and variance on a finite transcript cell. -/
def meanOn {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ x ∈ s, f x) / (s.card : ℝ)

def varianceOn {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  let mean := meanOn s f
  meanOn s (fun x => (f x - mean) ^ 2)

def cellMean (h : PartialAssignment n) (f : Cube n → ℝ) : ℝ :=
  meanOn (cell h) f

def cellVariance (h : PartialAssignment n) (f : Cube n → ℝ) : ℝ :=
  varianceOn (cell h) f

def cellStandardDeviation (h : PartialAssignment n)
    (f : Cube n → ℝ) : ℝ :=
  Real.sqrt (cellVariance h f)

def tableValue (table : BooleanTable n) : Cube n → ℝ :=
  fun x => signValue (table x)

def mixtureValue (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n) : Cube n → ℝ :=
  fun x => ∑ r : Fin N, p r * tableValue (tables r) x

def constantOnCell (h : PartialAssignment n) (f : Cube n → ℝ) : Prop :=
  ∀ x ∈ cell h, ∀ y ∈ cell h, f x = f y

def tableConstantOnCell (h : PartialAssignment n)
    (table : BooleanTable n) : Prop :=
  ∀ x ∈ cell h, ∀ y ∈ cell h, table x = table y

def tableNonconstantOnCell (h : PartialAssignment n)
    (table : BooleanTable n) : Prop :=
  ∃ x ∈ cell h, ∃ y ∈ cell h, table x ≠ table y

def activeComponentOnCell (tables : Fin N → BooleanTable n)
    (h : PartialAssignment n) : Prop :=
  ∃ r : Fin N, tableNonconstantOnCell h (tables r)

/-- The ordered transcript of a tree execution, including revealed answers. -/
def treeTranscript : BooleanTree n → Cube n → List (Fin n × RademacherSign)
  | .leaf _, _ => []
  | .query coordinate negative positive, x =>
      (coordinate, x coordinate) ::
        (if x coordinate then treeTranscript positive x
        else treeTranscript negative x)

def treeFiber (h : PartialAssignment n) (tree : BooleanTree n)
    (x : Cube n) : Finset (Cube n) :=
  (cell h).filter (fun y => treeTranscript tree y = treeTranscript tree x)

def conditionalVarianceGivenTree (h : PartialAssignment n)
    (tree : BooleanTree n) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  varianceOn (treeFiber h tree x) f

def conditionalStandardDeviationGivenTree (h : PartialAssignment n)
    (tree : BooleanTree n) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  Real.sqrt (conditionalVarianceGivenTree h tree f x)

/-- The potential `Phi(L)` on the current restricted cube. -/
def lawPotential (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n) (h : PartialAssignment n) : ℝ :=
  (∑ r : Fin N,
    p r * cellStandardDeviation h (tableValue (tables r))) ^ 2

def localBlockInequality (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n) (h : PartialAssignment n)
    (driver : Fin N) (tree : BooleanTree n) : Prop :=
  cellVariance h (mixtureValue p tables) +
      cellMean h (fun x =>
        (∑ r : Fin N,
          p r * conditionalStandardDeviationGivenTree h tree
            (tableValue (tables r)) x) ^ 2) ≤
    lawPotential p tables h

def validWeights (p : Fin N → ℝ) : Prop :=
  (∀ r, 0 ≤ p r) ∧ ∑ r : Fin N, p r = 1

def lawDepthAtMost (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n) (k : ℕ) : Prop :=
  ∀ r : Fin N, tableDepth (tables r) ≤ k

/-- The universal local premise of Theorem A, with a restricted cell written
as a partial assignment and `treeTranscript` representing `G_d`. -/
def universalBlockInequality (k : ℕ) : Prop :=
  ∀ (n N : ℕ) (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n) (h : PartialAssignment n),
    validWeights p ∧
      lawDepthAtMost p tables k ∧
      (cell h).Nonempty ∧
      activeComponentOnCell tables h →
      ∃ driver : Fin N, ∃ tree : BooleanTree n,
        tableNonconstantOnCell h (tables driver) ∧
          minimumRestrictedTree h (tables driver) tree ∧
          tree.depth ≤ k ∧
          localBlockInequality p tables h driver tree

/-- A policy that reveals one coordinate at each internal node. -/
inductive RevealPolicy (n : ℕ) where
  | stop
  | query (coordinate : Fin n)
      (negative positive : RevealPolicy n)

namespace RevealPolicy

def freshAt : RevealPolicy n → PartialAssignment n → Prop
  | .stop, _ => True
  | .query coordinate negative positive, h =>
      h coordinate = none ∧
        freshAt negative (updateAssignment h coordinate false) ∧
        freshAt positive (updateAssignment h coordinate true)

def determinesAt (policy : RevealPolicy n) (f : Cube n → ℝ)
    (h : PartialAssignment n) : Prop :=
  match policy with
  | .stop => constantOnCell h f
  | .query coordinate negative positive =>
      ¬ constantOnCell h f ∧
        h coordinate = none ∧
        determinesAt negative f (updateAssignment h coordinate false) ∧
        determinesAt positive f (updateAssignment h coordinate true)

def areaAt : RevealPolicy n → (Cube n → ℝ) → PartialAssignment n → ℝ
  | .stop, _, _ => 0
  | .query coordinate negative positive, f, h =>
      cellVariance h f +
        (areaAt negative f (updateAssignment h coordinate false) +
          areaAt positive f (updateAssignment h coordinate true)) / 2

end RevealPolicy

def rootAssignment : PartialAssignment n := fun _ => none

def legalPolicy (policy : RevealPolicy n) (f : Cube n → ℝ) : Prop :=
  policy.freshAt rootAssignment ∧
    policy.determinesAt f rootAssignment

def policyArea (policy : RevealPolicy n) (f : Cube n → ℝ) : ℝ :=
  policy.areaAt f rootAssignment

abbrev BlockChoice (n N : ℕ) :=
  PartialAssignment n → (Fin N × BooleanTree n)

/-- Compile the selected minimum-depth tree for one block into the
one-coordinate policy syntax. -/
def compileBlock {n : ℕ} :
    BooleanTree n →
      (PartialAssignment n → RevealPolicy n) →
      PartialAssignment n → RevealPolicy n
  | .leaf _, continuation, h => continuation h
  | .query coordinate negative positive, continuation, h =>
      .query coordinate
        (compileBlock negative continuation
          (updateAssignment h coordinate false))
        (compileBlock positive continuation
          (updateAssignment h coordinate true))

/-- Compile at most `fuel` driver blocks.  The extra fuel used below is the
finite-cube termination bound; valid blocks always consume a fresh coordinate. -/
noncomputable def compilePolicy {n N : ℕ}
    (p : Fin N → ℝ) (tables : Fin N → BooleanTable n)
    (choice : BlockChoice n N) :
    ℕ → PartialAssignment n → RevealPolicy n
  | 0, _ => .stop
  | fuel + 1, h =>
      if constantOnCell h (mixtureValue p tables) then
        .stop
      else
        compileBlock (choice h).2
          (fun h' => compilePolicy p tables choice fuel h') h

def validBlockChoice {n N : ℕ} (k : ℕ)
    (p : Fin N → ℝ) (tables : Fin N → BooleanTable n)
    (choice : BlockChoice n N) : Prop :=
  ∀ h, ¬ constantOnCell h (mixtureValue p tables) →
    let picked := choice h
    tableNonconstantOnCell h (tables picked.1) ∧
      minimumRestrictedTree h (tables picked.1) picked.2 ∧
      picked.2.depth ≤ k ∧
      localBlockInequality p tables h picked.1 picked.2

def theoremA : Prop :=
  ∀ k : ℕ, universalBlockInequality k →
    ∀ (n N : ℕ) (p : Fin N → ℝ)
      (tables : Fin N → BooleanTable n),
      validWeights p →
        lawDepthAtMost p tables k →
        ∃ choice : BlockChoice n N,
          validBlockChoice k p tables choice ∧
            let policy := compilePolicy p tables choice (n + 1) rootAssignment
            legalPolicy policy (mixtureValue p tables) ∧
              policyArea policy (mixtureValue p tables) ≤
                (k : ℝ) * (∑ r : Fin N, p r) ^ 2 ∧
              (k : ℝ) * (∑ r : Fin N, p r) ^ 2 ≤ (k : ℝ)

/-- Component masses and correlations in a restricted uniform cell. -/
def componentMass (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n)
    (h : PartialAssignment n) (r : Fin N) : ℝ :=
  p r * cellStandardDeviation h (tableValue (tables r))

def covarianceOnCell (h : PartialAssignment n)
    (f g : Cube n → ℝ) : ℝ :=
  cellMean h (fun x =>
    (f x - cellMean h f) * (g x - cellMean h g))

def componentCorrelation (tables : Fin N → BooleanTable n)
    (h : PartialAssignment n) (r d : Fin N) : ℝ :=
  if tableNonconstantOnCell h (tables r) ∧
      tableNonconstantOnCell h (tables d) then
    covarianceOnCell h (tableValue (tables r)) (tableValue (tables d)) /
      (cellStandardDeviation h (tableValue (tables r)) *
        cellStandardDeviation h (tableValue (tables d)))
  else 0

def driverDominatedAt (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n)
    (h : PartialAssignment n) (driver : Fin N) : Prop :=
  tableNonconstantOnCell h (tables driver) ∧
    (∑ r : Fin N, if r = driver then 0 else
      componentMass p tables h r *
        (1 + componentCorrelation tables h r driver)) ≤
      2 * componentMass p tables h driver

def hereditarilyDriverDominated (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n) : Prop :=
  ∀ h : PartialAssignment n,
    (cell h).Nonempty →
      activeComponentOnCell tables h →
        ∃ driver : Fin N, driverDominatedAt p tables h driver

/-- The unconditional local BSK conclusion supplied by the dominant-driver
condition (3). -/
def dominantDriverLocalTheorem : Prop :=
  ∀ (n N k : ℕ) (p : Fin N → ℝ)
    (tables : Fin N → BooleanTable n) (h : PartialAssignment n)
    (driver : Fin N) (tree : BooleanTree n),
    validWeights p →
      lawDepthAtMost p tables k →
        driverDominatedAt p tables h driver →
          minimumRestrictedTree h (tables driver) tree →
            tree.depth ≤ k →
              localBlockInequality p tables h driver tree

def dominantBlockChoice {n N : ℕ} (k : ℕ)
    (p : Fin N → ℝ) (tables : Fin N → BooleanTable n)
    (choice : BlockChoice n N) : Prop :=
  ∀ h, ¬ constantOnCell h (mixtureValue p tables) →
    let picked := choice h
    driverDominatedAt p tables h picked.1 ∧
      minimumRestrictedTree h (tables picked.1) picked.2 ∧
      picked.2.depth ≤ k ∧
      localBlockInequality p tables h picked.1 picked.2

def nonconstantComponentCount (tables : Fin N → BooleanTable n)
    (h : PartialAssignment n) : ℕ :=
  (Finset.univ.filter (fun r =>
    tableNonconstantOnCell h (tables r))).card

def theoremB : Prop :=
  dominantDriverLocalTheorem ∧
    (∀ (n N k : ℕ) (p : Fin N → ℝ)
      (tables : Fin N → BooleanTable n),
      validWeights p →
        lawDepthAtMost p tables k →
          hereditarilyDriverDominated p tables →
            ∃ choice : BlockChoice n N,
              dominantBlockChoice k p tables choice ∧
                let policy :=
                  compilePolicy p tables choice (n + 1) rootAssignment
                legalPolicy policy (mixtureValue p tables) ∧
                  policyArea policy (mixtureValue p tables) ≤
                    (k : ℝ) * (∑ r : Fin N, p r) ^ 2 ∧
                  (k : ℝ) * (∑ r : Fin N, p r) ^ 2 ≤ (k : ℝ)) ∧
    (∀ (n N : ℕ) (p : Fin N → ℝ)
      (tables : Fin N → BooleanTable n),
      validWeights p →
        nonconstantComponentCount tables rootAssignment ≤ 2 →
          hereditarilyDriverDominated p tables)

/-- The parity table, with `true` representing the positive sign. -/
def parityTable (k : ℕ) : BooleanTable k :=
  fun x => decide ((∑ i : Fin k, if x i then 0 else 1) % 2 = 0)

def liftPolicy {n : ℕ} :
    RevealPolicy n → RevealPolicy (n + 1)
  | .stop => .stop
  | .query coordinate negative positive =>
      .query coordinate.succ (liftPolicy negative) (liftPolicy positive)

def allCoordinatesPolicy : (k : ℕ) → RevealPolicy k
  | 0 => .stop
  | k + 1 =>
      .query 0 (liftPolicy (allCoordinatesPolicy k))
        (liftPolicy (allCoordinatesPolicy k))

def parityValue (k : ℕ) : Cube k → ℝ :=
  tableValue (parityTable k)

def paritySharpness : Prop :=
  ∀ k : ℕ,
    tableDepth (parityTable k) = k ∧
      legalPolicy (allCoordinatesPolicy k) (parityValue k) ∧
        policyArea (allCoordinatesPolicy k) (parityValue k) = (k : ℝ) ∧
        ∀ policy : RevealPolicy k,
          legalPolicy policy (parityValue k) →
            (k : ℝ) ≤ policyArea policy (parityValue k)

/-- Claim 61311: the exact block-potential reduction, the unconditional
hereditary dominant-driver class, its two-component corollary, and parity
sharpness on finite uniform Rademacher cubes. -/
def claim61311 : Prop :=
  (∀ (n N : ℕ) (p : Fin N → ℝ)
      (tables : Fin N → BooleanTable n),
      validWeights p →
        lawPotential p tables rootAssignment ≤
          (∑ r : Fin N, p r) ^ 2) ∧
    theoremA ∧ theoremB ∧ paritySharpness

end

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaBlockPotential61311
