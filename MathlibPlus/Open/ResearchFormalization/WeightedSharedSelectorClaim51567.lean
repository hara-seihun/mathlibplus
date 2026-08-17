import MathlibPlus.Open.ResearchFormalization.R3630

open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MathlibPlus.Open.ResearchFormalization.WeightedSharedSelectorClaim51567

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R3630

private def boolSign (b : Bool) : ℝ :=
  if b then 1 else -1

private def selectorCoordinate {n : ℕ} (i : Fin n) : Fin (n + 2) :=
  Fin.succ (Fin.succ i)

private def selectorTarget (n : ℕ) (weights : Fin n → ℝ)
    (ω : RademacherCube (n + 2)) : ℝ :=
  ∑ i : Fin n, weights i *
    (if ω (selectorCoordinate i) then boolSign (ω 1) else boolSign (ω 0))

private def selectorSum (n : ℕ) (weights : Fin n → ℝ)
    (ω : RademacherCube (n + 2)) : ℝ :=
  ∑ i : Fin n, weights i * boolSign (ω (selectorCoordinate i))

private def nonincreasing {n : ℕ} (b : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i.1 ≤ j.1 → b j ≤ b i

private def tailArea {n : ℕ} (b : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ((i.1 : ℝ) + 1) * b i ^ 2

private def linearTarget {n : ℕ} (b : Fin n → ℝ)
    (ω : RademacherCube n) : ℝ :=
  ∑ i : Fin n, b i * boolSign (ω i)

/-- Claim 51567: the normalized shared-selector affine identity, the exact
root-inclusive area of the decreasing-coordinate policy for a finite linear
list, and the elementary quadratic tail bound. -/
def claim51567 : Prop :=
  (∀ (n : ℕ) (weights : Fin n → ℝ)
      (ω : RademacherCube (n + 2)),
      (∀ i, 0 ≤ weights i) →
      (∑ i, weights i = 1) →
      let S := selectorSum n weights ω
      selectorTarget n weights ω =
        (boolSign (ω 0) + boolSign (ω 1)) / 2 +
          (boolSign (ω 1) - boolSign (ω 0)) / 2 * S) ∧
    (∀ (n : ℕ) (b : Fin n → ℝ),
      (∀ i, 0 ≤ b i) →
      nonincreasing b →
      let L := tailArea b
      ∃ tree : DecisionTree n,
        terminalTree (linearTarget b) tree ∧
          (∀ x : RademacherCube n,
            treeQueryPath tree (treePath tree x) =
              List.ofFn (fun i : Fin n => i)) ∧
          realTreeArea tree (linearTarget b) = L ∧
          L ≤ (∑ i : Fin n, b i) ^ 2)

end

end MathlibPlus.Open.ResearchFormalization.WeightedSharedSelectorClaim51567
