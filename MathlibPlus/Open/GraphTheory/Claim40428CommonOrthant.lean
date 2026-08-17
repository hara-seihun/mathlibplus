import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.ResearchCubeDefectThresholdClaim40428

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev CubeDirections (n : ℕ) := Fin n → (Cube n → Bool)

def cubeFlip {n : ℕ} (x : Cube n) (j : Fin n) : Cube n :=
  Function.update x j (!(x j))

def directionIndependent {n : ℕ} (f : CubeDirections n) (i : Fin n) : Prop :=
  ∀ x : Cube n, f i (cubeFlip x i) = f i x

def validCubeDirections {n : ℕ} (f : CubeDirections n) : Prop :=
  ∀ i, directionIndependent f i

def cubeFiber {n : ℕ} (j : Fin n) : Finset (Cube n) :=
  Finset.univ.filter (fun x => x j = false)

def cubeAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x : Cube n, g x) / ((2 : ℝ) ^ n)

def cubeFiberAverage {n : ℕ} (j : Fin n) (g : Cube n → ℝ) : ℝ :=
  (∑ x ∈ cubeFiber j, g x) / ((2 : ℝ) ^ (n - 1))

def directionDensity {n : ℕ} (f : CubeDirections n) (i : Fin n) : ℝ :=
  cubeAverage (fun x => if f i x then 1 else 0)

def upwardTransition {n : ℕ} (f : CubeDirections n) (i j : Fin n) : ℝ :=
  cubeFiberAverage j (fun x =>
    if f i x = false ∧ f i (cubeFlip x j) = true then 1 else 0)

def downwardTransition {n : ℕ} (f : CubeDirections n) (i j : Fin n) : ℝ :=
  cubeFiberAverage j (fun x =>
    if f i x = true ∧ f i (cubeFlip x j) = false then 1 else 0)

def transitionDefect {n : ℕ} (f : CubeDirections n) (i j : Fin n) : ℝ :=
  min (upwardTransition f i j) (downwardTransition f i j)

def cubeGraph {n : ℕ} (f : CubeDirections n) : SimpleGraph (Cube n) :=
  SimpleGraph.fromRel (fun x y =>
    ∃ i : Fin n, x i = false ∧ y = cubeFlip x i ∧ f i x = true)

def cubeC4Free {n : ℕ} (f : CubeDirections n) : Prop :=
  ¬ ∃ a b c d : Cube n,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      (cubeGraph f).Adj a b ∧ (cubeGraph f).Adj b c ∧
      (cubeGraph f).Adj c d ∧ (cubeGraph f).Adj d a

def chosenOrientation {n : ℕ} (f : CubeDirections n) (i j : Fin n) : Bool :=
  if upwardTransition f i j ≤ downwardTransition f i j then true else false

def pairColor {n : ℕ} (f : CubeDirections n) (i j : Fin n) : Bool × Bool :=
  (chosenOrientation f i j, chosenOrientation f j i)

def commonOrthantBlock {n : ℕ} (f : CubeDirections n)
    (I : Finset (Fin n)) : Prop :=
  ∃ c : Bool × Bool, c.1 = c.2 ∧
    ∀ i ∈ I, ∀ j ∈ I, i < j → pairColor f i j = c

def aggregateDefect {n : ℕ} (f : CubeDirections n)
    (I : Finset (Fin n)) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I.erase i, transitionDefect f i j

def blockDensitySum {n : ℕ} (f : CubeDirections n)
    (I : Finset (Fin n)) : ℝ :=
  ∑ i ∈ I, directionDensity f i

/-- The robust common-orthant estimate for the exact literal C4-free cube
carrier.  `commonOrthantBlock` records both the increasing and reflected
common choices through the cheaper transition orientation. -/
def robustCommonOrthantBlock_claim40428 : Prop :=
  ∀ (n : ℕ) (f : CubeDirections n) (I : Finset (Fin n)),
    validCubeDirections f → cubeC4Free f → commonOrthantBlock f I →
    blockDensitySum f I ≤ 2 + aggregateDefect f I / 2

end
end MathlibPlus.Open.GraphTheory.ResearchCubeDefectThresholdClaim40428
