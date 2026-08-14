import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.Research.FormalizationBatch

private def squarefreeNat (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

private noncomputable def squarefreeVertices (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter squarefreeNat

private def mobiusSign (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1 : ℤ) ^ n.primeFactorsList.length

private def onePrimeToggle (a b : ℕ) : Prop :=
  (a ∣ b ∧ Nat.Prime (b / a)) ∨
  (b ∣ a ∧ Nat.Prime (a / b))

private noncomputable def toggleEdges (X : ℕ) : Finset (ℕ × ℕ) :=
  (squarefreeVertices X).product (squarefreeVertices X) |>.filter fun e =>
    onePrimeToggle e.1 e.2 ∧ mobiusSign e.1 = -mobiusSign e.2

private noncomputable def isMatchingFor (X : ℕ) (M : Finset (ℕ × ℕ)) : Prop :=
  M ⊆ toggleEdges X ∧
    ∀ v : ℕ, (M.filter fun e => e.1 = v ∨ e.2 = v).card ≤ 1

private noncomputable def matchingFamily (X : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (toggleEdges X).powerset.filter (isMatchingFor X)

private noncomputable def maximumMatchingCard (X : ℕ) : ℕ :=
  (matchingFamily X).sup Finset.card

private noncomputable def matchingDeficiency (X : ℕ) : ℕ :=
  (squarefreeVertices X).card - 2 * maximumMatchingCard X

private noncomputable def positiveColorCount (X : ℕ) : ℕ :=
  ((squarefreeVertices X).filter fun n => mobiusSign n = 1).card

private noncomputable def negativeColorCount (X : ℕ) : ℕ :=
  ((squarefreeVertices X).filter fun n => mobiusSign n = -1).card

private noncomputable def colorImbalance (X : ℕ) : ℕ :=
  Nat.dist (positiveColorCount X) (negativeColorCount X)

/-- The finite graph has exactly the squarefree vertices and one-prime-toggle edges. -/
def squarefreeOnePrimeToggleGraph : Prop :=
  ∀ X : ℕ,
    (∀ n : ℕ,
      n ∈ squarefreeVertices X ↔
        0 < n ∧ n ≤ X ∧ squarefreeNat n) ∧
    (∀ a b : ℕ,
      (a, b) ∈ toggleEdges X ↔
        a ∈ squarefreeVertices X ∧
        b ∈ squarefreeVertices X ∧
        onePrimeToggle a b ∧ mobiusSign a = -mobiusSign b)

/-- Uniform half-width r=1/20971520 forces the stated cover-count lower bound. -/
def uniformRadiusCoverCount : Prop :=
  ∀ (N : ℕ) (centers : Fin N → ℝ),
    (∀ x : ℝ,
      (1 / 10 : ℝ) ≤ x → x ≤ 6 →
        ∃ i : Fin N, |x - centers i| ≤ (1 : ℝ) / 20971520) →
    61865984 ≤ N

/-- The exact unmatched-vertex and absolute-color-imbalance table. -/
def exactMaximumMatchingDeficiencyTable : Prop :=
  matchingDeficiency 100 = 19 ∧ colorImbalance 100 = 1 ∧
  matchingDeficiency 1000 = 164 ∧ colorImbalance 1000 = 2 ∧
  matchingDeficiency 10000 = 1685 ∧ colorImbalance 10000 = 23 ∧
  matchingDeficiency 100000 = 16674 ∧ colorImbalance 100000 = 48 ∧
  matchingDeficiency 300000 = 50132 ∧ colorImbalance 300000 = 220

/-- At 300000 the matching defect is strictly larger than global color imbalance. -/
def onePrimeToggleHallDefect : Prop :=
  matchingDeficiency 300000 = 50132 ∧
  colorImbalance 300000 = 220 ∧
  colorImbalance 300000 < matchingDeficiency 300000

/-- The tested one-toggle graph leaves more than one sixth of its vertices unmatched. -/
def literalOneToggleFiniteFailure : Prop :=
  matchingDeficiency 300000 = 50132 ∧
  6 * matchingDeficiency 300000 > (squarefreeVertices 300000).card

end MathlibPlus.Open.Research.FormalizationBatch
