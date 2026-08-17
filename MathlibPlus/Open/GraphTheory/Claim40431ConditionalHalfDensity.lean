import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.ResearchCubeDefectThreshold

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev Cube (n : ℕ) := Fin n → Bool
private abbrev CubeDirections (n : ℕ) := Fin n → (Cube n → Bool)

private def cubeFlip {n : ℕ} (x : Cube n) (j : Fin n) : Cube n :=
  Function.update x j (!(x j))

private def directionIndependent {n : ℕ} (f : CubeDirections n) (i : Fin n) : Prop :=
  ∀ x : Cube n, f i (cubeFlip x i) = f i x

private def validCubeDirections {n : ℕ} (f : CubeDirections n) : Prop :=
  ∀ i, directionIndependent f i

private def cubeFiber {n : ℕ} (j : Fin n) : Finset (Cube n) :=
  Finset.univ.filter (fun x => x j = false)

private def cubeAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x : Cube n, g x) / ((2 : ℝ) ^ n)

private def cubeFiberAverage {n : ℕ} (j : Fin n) (g : Cube n → ℝ) : ℝ :=
  (∑ x ∈ cubeFiber j, g x) / ((2 : ℝ) ^ (n - 1))

private def directionDensity {n : ℕ} (f : CubeDirections n) (i : Fin n) : ℝ :=
  cubeAverage (fun x => if f i x then 1 else 0)

private def upwardTransition {n : ℕ} (f : CubeDirections n) (i j : Fin n) : ℝ :=
  cubeFiberAverage j (fun x =>
    if f i x = false ∧ f i (cubeFlip x j) = true then 1 else 0)

private def downwardTransition {n : ℕ} (f : CubeDirections n) (i j : Fin n) : ℝ :=
  cubeFiberAverage j (fun x =>
    if f i x = true ∧ f i (cubeFlip x j) = false then 1 else 0)

private def transitionDefect {n : ℕ} (f : CubeDirections n) (i j : Fin n) : ℝ :=
  min (upwardTransition f i j) (downwardTransition f i j)

private def cubeGraph {n : ℕ} (f : CubeDirections n) : SimpleGraph (Cube n) :=
  SimpleGraph.fromRel (fun x y =>
    ∃ i : Fin n, x i = false ∧ y = cubeFlip x i ∧ f i x = true)

private def cubeC4Free {n : ℕ} (f : CubeDirections n) : Prop :=
  ¬ ∃ a b c d : Cube n,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      (cubeGraph f).Adj a b ∧ (cubeGraph f).Adj b c ∧
      (cubeGraph f).Adj c d ∧ (cubeGraph f).Adj d a

private def heavyDirections {n : ℕ} (f : CubeDirections n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => directionDensity f i > 1 / 2)

private def aggregateDefect {n : ℕ} (f : CubeDirections n) (I : Finset (Fin n)) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I.erase i, transitionDefect f i j

private def cubeEdgeCount {n : ℕ} (f : CubeDirections n) : ℝ :=
  ((2 : ℝ) ^ (n - 1)) * ∑ i : Fin n, directionDensity f i

/-- A sublinear heavy-direction charge conditionally yields the half-density
asymptotic edge bound; the charge hypothesis is not derived from C4-freeness. -/
def conditionalHalfDensity_claim40431 : Prop :=
  ∀ (F : ∀ n : ℕ, CubeDirections n),
    (∀ n, validCubeDirections (F n) ∧ cubeC4Free (F n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      aggregateDefect (F n) (heavyDirections (F n)) < ε * n) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      cubeEdgeCount (F n) ≤ (1 / 2 + ε) * n * (2 : ℝ) ^ (n - 1))

end
end MathlibPlus.Open.GraphTheory.ResearchCubeDefectThreshold
