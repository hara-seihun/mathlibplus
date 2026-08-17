import MathlibPlus.Open.Probability.ResearchBatch

namespace MathlibPlus.Open.ResearchFormalization.R2933Claim47500

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.Probability.ResearchBatch

abbrev Cube3 := Cube 3
abbrev Table := Cube3 → ℝ

private def lexTable
    (a0 a1 a2 a3 a4 a5 a6 a7 : ℝ) : Table :=
  fun x =>
    if x 0 then
      if x 1 then
        if x 2 then a7 else a6
      else
        if x 2 then a5 else a4
    else
      if x 1 then
        if x 2 then a3 else a2
      else
        if x 2 then a1 else a0

private def L : Table :=
  lexTable (-1) (-1) (-1) (-1) 0 0 1 1

private def R : Table :=
  lexTable (-1) (-1) 0 0 (-1) (-1) 1 1

private def M : Table :=
  lexTable (-1) (-1) (-1 / 2) (-1 / 2) (-1 / 2) (-1 / 2) 1 1

abbrev BooleanTable (n : ℕ) :=
  {h : Cube n → ℝ // ∀ x, h x = 1 ∨ h x = -1}

abbrev BooleanLaw (n : ℕ) := List (BooleanTable n × ℝ)

private def lawWeightSum (law : BooleanLaw 3) : ℝ :=
  (law.map Prod.snd).sum

private def lawNonnegative (law : BooleanLaw 3) : Prop :=
  ∀ entry ∈ law, 0 ≤ entry.2

private def isProbabilityLaw (law : BooleanLaw 3) : Prop :=
  lawNonnegative law ∧ lawWeightSum law = 1

private def lawBarycenter (law : BooleanLaw 3) : Table :=
  fun x => (law.map (fun entry => entry.2 * entry.1.1 x)).sum

private def convexCombinationOfBooleanTables (g : Table) : Prop :=
  ∃ law : BooleanLaw 3,
    isProbabilityLaw law ∧
      ∀ x : Cube3, lawBarycenter law x = g x

private def inUnitCube (g : Table) : Prop :=
  ∀ x : Cube3, g x ∈ Set.Icc (-1 : ℝ) 1

private def queryDepth {n : ℕ} : QueryTree n → ℕ
  | .leaf => 0
  | .node _ left right => 1 + max (queryDepth left) (queryDepth right)

private def fullTree3 : QueryTree 3 :=
  .node 0
    (.node 1 (.node 2 .leaf .leaf) (.node 2 .leaf .leaf))
    (.node 1 (.node 2 .leaf .leaf) (.node 2 .leaf .leaf))

private def everyBooleanTableHasDepthThreeTree : Prop :=
  queryDepth fullTree3 = 3 ∧
    valid fullTree3 ∧
      ∀ h : BooleanTable 3, complete h.1 fullTree3

private def boundedTablesHaveBooleanMixtures : Prop :=
  ∀ g : Table, inUnitCube g → convexCombinationOfBooleanTables g

private def exactAreas : Prop :=
  optimalArea L = (13 : ℝ) / 16 ∧
    optimalArea R = (13 : ℝ) / 16 ∧
    optimalArea M = (7 : ℝ) / 8 ∧
    optimalArea L < 3 ∧ optimalArea R < 3 ∧ optimalArea M < 3

private def midpointData : Prop :=
  (∀ x : Cube3, M x = (L x + R x) / 2) ∧
    (∀ x : Cube3, L x ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ x : Cube3, R x ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ x : Cube3, M x ∈ Set.Icc (-1 : ℝ) 1)

/-- Claim 47500: the displayed non-Boolean tables are bounded finite targets,
lie in the convex hull of Boolean three-bit tables, and have Bellman
posterior-variance area below the depth-three budget. -/
def claim47500 : Prop :=
  midpointData ∧
    boundedTablesHaveBooleanMixtures ∧
    convexCombinationOfBooleanTables L ∧
    convexCombinationOfBooleanTables R ∧
    convexCombinationOfBooleanTables M ∧
    everyBooleanTableHasDepthThreeTree ∧
    exactAreas

end
end MathlibPlus.Open.ResearchFormalization.R2933Claim47500
