import Mathlib

noncomputable section
universe u

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-! The sign set `{−1, 1}` used by the oracle and the matrix rows. -/
def Sign := {s : ℝ // s = -1 ∨ s = 1}

/-! Finite deterministic coordinate decision trees. -/
inductive QueryTree (I : Type u) where
  | leaf : Sign → QueryTree I
  | query : I → QueryTree I → QueryTree I → QueryTree I

namespace QueryTree

protected def evaluate : QueryTree I → (I → Sign) → Sign
  | .leaf s, _ => s
  | .query i left right, oracle =>
      if (oracle i).val = -1 then left.evaluate oracle else right.evaluate oracle

protected def queryCount : QueryTree I → (I → Sign) → ℕ
  | .leaf _, _ => 0
  | .query i left right, oracle =>
      1 + if (oracle i).val = -1 then left.queryCount oracle else right.queryCount oracle

def noRepeatedFrom (seen : Set I) : QueryTree I → Prop
  | .leaf _ => True
  | .query i left right =>
      i ∉ seen ∧ noRepeatedFrom (insert i seen) left ∧ noRepeatedFrom (insert i seen) right

def Legal (tree : QueryTree I) : Prop := noRepeatedFrom (∅ : Set I) tree

end QueryTree

/-! Finite-sum expectations and the row quantities in the admitted communication claim. -/
def rowExpectedCommunication {I : Type u}
    (p : ℕ → ℝ) (trees : ℕ → QueryTree I) (oracle : I → Sign) : ℝ :=
  ∑' n : ℕ, p n * (trees n).queryCount oracle

def rowEstimator {I : Type u}
    (p : ℕ → ℝ) (rows : ℕ → (I → Sign) → Sign) (oracle : I → Sign) : ℝ :=
  ∑' n : ℕ, p n * (rows n oracle).val

def stoppedRowEstimator {I : Type u}
    (p : ℕ → ℝ) (trees : ℕ → QueryTree I) (rows : ℕ → (I → Sign) → Sign)
    (oracle : I → Sign) (m : ℕ) : ℝ :=
  ∑' n : ℕ,
    if (trees n).queryCount oracle ≤ m then p n * (rows n oracle).val else 0

def estimatorError {I : Type u}
    (p : ℕ → ℝ) (trees : ℕ → QueryTree I) (rows : ℕ → (I → Sign) → Sign)
    (oracle : I → Sign) (m : ℕ) : ℝ :=
  |rowEstimator p rows oracle - stoppedRowEstimator p trees rows oracle m|

def tailMass {I : Type u}
    (p : ℕ → ℝ) (trees : ℕ → QueryTree I) (oracle : I → Sign) (m : ℕ) : ℝ :=
  ∑' n : ℕ, if m < (trees n).queryCount oracle then p n else 0

def squareArea {I : Type u}
    (p : ℕ → ℝ) (trees : ℕ → QueryTree I) (rows : ℕ → (I → Sign) → Sign)
    (oracle : I → Sign) : ℝ :=
  ∑' m : ℕ, (estimatorError p trees rows oracle m) ^ 2

def tailSquareArea {I : Type u}
    (p : ℕ → ℝ) (trees : ℕ → QueryTree I) (oracle : I → Sign) : ℝ :=
  ∑' m : ℕ, (tailMass p trees oracle m) ^ 2

/--
The exact countable-row, unbounded-depth square-area assertion from Claim 59952.
The tree datatype makes every individual row finite; the family is not given a
uniform depth bound.
-/
def countableRowTreeSquareAreaBound : Prop :=
  ∀ {I : Type u} (p : ℕ → ℝ) (trees : ℕ → QueryTree I)
    (rows : ℕ → (I → Sign) → Sign),
    (∀ n, 0 ≤ p n) →
    (∑' n : ℕ, p n = 1) →
    (∀ n, (trees n).Legal) →
    (∀ n oracle, rows n oracle = (trees n).evaluate oracle) →
    (∀ oracle, Summable (fun n : ℕ => p n * ((trees n).queryCount oracle : ℝ))) →
    (∀ oracle,
      squareArea p trees rows oracle ≤ tailSquareArea p trees oracle ∧
      tailSquareArea p trees oracle ≤
        (∑' m : ℕ, tailMass p trees oracle m) ∧
      (∑' m : ℕ, tailMass p trees oracle m) = rowExpectedCommunication p trees oracle) ∧
    ∀ (k : ℝ),
      (∀ oracle, rowExpectedCommunication p trees oracle ≤ k) →
      ∀ oracle, squareArea p trees rows oracle ≤ k


end MathlibPlus.Open.ResearchFormalizationBatch
