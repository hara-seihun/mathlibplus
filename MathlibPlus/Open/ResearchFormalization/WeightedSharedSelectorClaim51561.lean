import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.WeightedSharedSelectorClaim51561

noncomputable section

private def boolSign (b : Bool) : ℝ := if b then 1 else -1

private abbrev BoolCube (n : ℕ) := Fin n → Bool

private def conditionalVariance {n : ℕ}
    (F : BoolCube n → ℝ) (known : Finset (Fin n))
    (ω : BoolCube n) : ℝ :=
  let fibre : Finset (BoolCube n) :=
    Finset.univ.filter (fun ω' => ∀ i ∈ known, ω' i = ω i)
  let denominator : ℝ := fibre.card
  let mean : ℝ := fibre.sum F / denominator
  fibre.sum (fun ω' => (F ω' - mean) ^ 2) / denominator

private def expectedVariance {n : ℕ}
    (F : BoolCube n → ℝ) (known : Finset (Fin n)) : ℝ :=
  (∑ ω : BoolCube n, conditionalVariance F known ω) /
    (Fintype.card (BoolCube n) : ℝ)

private def pathArea {n : ℕ}
    (F : BoolCube n → ℝ) (queries : List (Fin n))
    (ω : BoolCube n) : ℝ :=
  ((queries.foldl
      (fun state q =>
        if conditionalVariance F state.1 ω = 0 then state
        else
          (insert q state.1,
            state.2 + conditionalVariance F state.1 ω))
      (∅, (0 : ℝ))).2)

private def policyArea {n : ℕ}
    (F : BoolCube n → ℝ)
    (queries : BoolCube n → List (Fin n)) : ℝ :=
  (∑ ω : BoolCube n, pathArea F (queries ω) ω) /
    (Fintype.card (BoolCube n) : ℝ)

private def selectorCoord {n : ℕ} (i : Fin n) : Fin (n + 2) :=
  Fin.succ (Fin.succ i)

private def selectorTarget (n : ℕ) (weights : Fin n → ℝ)
    (ω : BoolCube (n + 2)) : ℝ :=
  ∑ i : Fin n, weights i *
    (if ω (selectorCoord i) then boolSign (ω 1) else boolSign (ω 0))

private def selectorSum (n : ℕ) (weights : Fin n → ℝ)
    (ω : BoolCube (n + 2)) : ℝ :=
  ∑ i : Fin n, weights i * boolSign (ω (selectorCoord i))

private def listFromPerm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    List (Fin (n + 2)) :=
  List.ofFn (fun i : Fin n => selectorCoord (p i))

private def descending {n : ℕ} (weights : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val ≤ j.val → weights (p j) ≤ weights (p i)

private def tailArea {n : ℕ} (weights : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, ((i.val : ℝ) + 1) * weights (p i) ^ 2

private def sharedQueries {n : ℕ} (p : Equiv.Perm (Fin n))
    (ω : BoolCube (n + 2)) : List (Fin (n + 2)) :=
  [0, 1] ++ if ω 0 = ω 1 then [] else listFromPerm p

private def dominantQueriesAt {n : ℕ} (d : Fin n)
    (p : Equiv.Perm (Fin n)) (ω : BoolCube (n + 2)) : List (Fin (n + 2)) :=
  let selected : Fin (n + 2) := if ω (selectorCoord d) then 1 else 0
  let other : Fin (n + 2) := if ω (selectorCoord d) then 0 else 1
  [selectorCoord d, selected, other] ++
    if ω 0 = ω 1 then []
    else (listFromPerm p).filter (fun q => q ≠ selectorCoord d)

private def globalLevel {n : ℕ} (i : Fin (n + 2)) : ℕ :=
  if i = 0 ∨ i = 1 then 2 else 1

private def dominantQueriesResidual {n : ℕ}
    (p : Equiv.Perm (Fin n)) (ω : BoolCube (n + 3)) :
    List (Fin (n + 3)) :=
  let root : Fin (n + 3) := selectorCoord (0 : Fin (n + 1))
  let selected : Fin (n + 3) := if ω root then 1 else 0
  let other : Fin (n + 3) := if ω root then 0 else 1
  [root, selected, other] ++
    if ω 0 = ω 1 then []
    else List.ofFn (fun i : Fin n => selectorCoord (Fin.succ (p i)))

private def maxWitness {n : ℕ} (weights : Fin n → ℝ) (a : ℝ) : Prop :=
  (∀ i : Fin n, weights i ≤ a) ∧ ∃ i : Fin n, weights i = a

private def linearTarget {n : ℕ} (weights : Fin n → ℝ)
    (ω : BoolCube n) : ℝ :=
  ∑ i : Fin n, weights i * boolSign (ω i)

private def linearQueries {n : ℕ} (_ : BoolCube n) : List (Fin n) :=
  List.ofFn (fun i : Fin n => i)

private def dominantWeights (a : ℝ) {n : ℕ} (b : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.cases a b

private def selectedSharedVariance {n : ℕ}
    (F : BoolCube (n + 2) → ℝ) (d : Fin n) : ℝ :=
  let root : Fin (n + 2) := selectorCoord d
  (∑ ω : BoolCube (n + 2),
      conditionalVariance F
        (insert (if ω root then 1 else 0) {root}) ω) /
    (Fintype.card (BoolCube (n + 2)) : ℝ)

/-- Claim 51561: the exact independent-sign shared-selector family has the
stated level assignment and one of the two displayed adaptive policies. -/
def claim51561 : Prop :=
  ∀ (n : ℕ) (weights : Fin n → ℝ),
    (∀ i, 0 ≤ weights i) →
    (∑ i, weights i = 1) →
    let F : BoolCube (n + 2) → ℝ := selectorTarget n weights
    (∀ i : Fin n, globalLevel (selectorCoord i) = 1) ∧
      globalLevel (0 : Fin (n + 2)) = 2 ∧
      globalLevel (1 : Fin (n + 2)) = 2 ∧
      (∃ p : Equiv.Perm (Fin n),
        descending weights p ∧
          ((∃ a : ℝ,
              maxWitness weights a ∧ a ≤ 1 / 2 ∧
                (∀ ω, (sharedQueries p ω).Nodup) ∧
                policyArea F (sharedQueries p) ≤ 2) ∨
            (∃ d : Fin n, ∃ a : ℝ,
              weights d = a ∧ (∀ i, weights i ≤ a) ∧ a ≥ 1 / 2 ∧
                (∀ ω, (dominantQueriesAt d p ω).Nodup) ∧
                policyArea F (dominantQueriesAt d p) ≤ 2)))


end

end MathlibPlus.Open.ResearchFormalization.WeightedSharedSelectorClaim51561
