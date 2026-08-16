import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.OracleArea.Claim60107

abbrev RademacherSign := Bool

namespace RademacherSign

def value (s : RademacherSign) : ℝ :=
  if s then 1 else -1

end RademacherSign

inductive CoordinateTree (ι : Type) where
  | leaf : ι → CoordinateTree ι
  | branch : ι → CoordinateTree ι → CoordinateTree ι → CoordinateTree ι

namespace CoordinateTree

def eval : CoordinateTree ι → (ι → RademacherSign) → RademacherSign
  | .leaf i, ω => ω i
  | .branch i positive negative, ω =>
      if ω i then eval positive ω else eval negative ω

def depth : CoordinateTree ι → ℕ
  | .leaf _ => 1
  | .branch _ positive negative => 1 + max positive.depth negative.depth

end CoordinateTree

abbrev Coordinate := Fin 3
abbrev Oracle := Coordinate → RademacherSign
abbrev History := Coordinate → Option RademacherSign

private def treeA : CoordinateTree Coordinate :=
  .branch 0 (.leaf 1) (.leaf 2)

private def treeB : CoordinateTree Coordinate :=
  .branch 1 (.leaf 0) (.leaf 2)

private def evaluateA (ω : Oracle) : RademacherSign := treeA.eval ω
private def evaluateB (ω : Oracle) : RademacherSign := treeB.eval ω

private def emptyHistory : History := fun _ => none

private def reveal (h : History) (c : Coordinate) (ω : Oracle) : History :=
  Function.update h c (some (ω c))

structure CoordinatePolicy where
  next : History → Option Coordinate

private def LegalPolicy (p : CoordinatePolicy) : Prop :=
  ∀ (h : History) (c : Coordinate), p.next h = some c → h c = none

private def transcript (p : CoordinatePolicy) (ω : Oracle) : ℕ → History
  | 0 => emptyHistory
  | m + 1 =>
      let h := transcript p ω m
      match p.next h with
      | none => h
      | some c => reveal h c ω

private def consistent (h : History) (ω : Oracle) : Prop :=
  ∀ (c : Coordinate) (s : RademacherSign), h c = some s → ω c = s

private noncomputable def fiber (h : History) : Finset Oracle := by
  classical
  exact Finset.univ.filter (fun ω => consistent h ω)

private noncomputable def posteriorVariance (f : Oracle → ℝ) (h : History) : ℝ :=
  let S := fiber h
  if S.Nonempty then
    let n : ℝ := S.card
    (∑ ω ∈ S, (f ω) ^ 2) / n - ((∑ ω ∈ S, f ω) / n) ^ 2
  else
    0

private noncomputable def expectedPosteriorVariance
    (f : Oracle → ℝ) (h : Oracle → History) : ℝ :=
  (∑ ω : Oracle, posteriorVariance f (h ω)) / (Fintype.card Oracle : ℝ)

private noncomputable def rootInclusiveArea
    (p : CoordinatePolicy) (f : Oracle → ℝ) : ℝ :=
  ∑ m : Fin 4, expectedPosteriorVariance f (fun ω => transcript p ω m.val)

private def policyPX : CoordinatePolicy :=
  { next := fun h =>
      if h 0 = none then
        some 0
      else if h 0 = some true then
        if h 1 = none then some 1
        else if h 2 = none then some 2
        else none
      else
        if h 2 = none then some 2
        else if h 1 = none then some 1
        else none }

private def policyPY : CoordinatePolicy :=
  { next := fun h =>
      if h 1 = none then
        some 1
      else if h 1 = some true then
        if h 0 = none then some 0
        else if h 2 = none then some 2
        else none
      else
        if h 2 = none then some 2
        else if h 0 = none then some 0
        else none }

private noncomputable def mixtureTarget (l : ℝ) (ω : Oracle) : ℝ :=
  l * RademacherSign.value (evaluateA ω) +
    (1 - l) * RademacherSign.value (evaluateB ω)

private noncomputable def pxFormula (l : ℝ) : ℝ :=
  (9 * l ^ 2 - 10 * l + 9) / 4

private noncomputable def pyFormula (l : ℝ) : ℝ :=
  (9 * l ^ 2 - 8 * l + 8) / 4

/-- Exact finite-product formalization of the mixed-root depth-two claim. -/
def claim60107 : Prop :=
  ∀ l : ℝ, 0 ≤ l ∧ l ≤ 1 →
    LegalPolicy policyPX ∧
    LegalPolicy policyPY ∧
    rootInclusiveArea policyPX (mixtureTarget l) = pxFormula l ∧
    rootInclusiveArea policyPY (mixtureTarget l) = pyFormula l ∧
    2 - rootInclusiveArea policyPX (mixtureTarget l) =
      ((1 - l) * (9 * l - 1)) / 4 ∧
    2 - rootInclusiveArea policyPY (mixtureTarget l) =
      (l * (8 - 9 * l)) / 4 ∧
    (1 / 9 ≤ l → rootInclusiveArea policyPX (mixtureTarget l) ≤ 2) ∧
    (l ≤ 8 / 9 → rootInclusiveArea policyPY (mixtureTarget l) ≤ 2) ∧
    ((l ≤ 8 / 9) ∨ (1 / 9 ≤ l)) ∧
    (∃ p : CoordinatePolicy,
      LegalPolicy p ∧ rootInclusiveArea p (mixtureTarget l) ≤ 2)

end MathlibPlus.Open.OracleArea.Claim60107
