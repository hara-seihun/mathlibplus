import Mathlib

namespace MathlibPlus.MomentGeometry

open Matrix
open scoped BigOperators

/-- A finite index selection is in inherited order when each adjacent index increases. -/
def IsIncreasingSelection {k : ℕ} {α : Type*} [LT α] (f : Fin (k + 1) → α) : Prop :=
  ∀ i : Fin k, f i.castSucc < f i.succ

instance {k : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (f : Fin (k + 1) → α) :
    Decidable (IsIncreasingSelection f) := by
  unfold IsIncreasingSelection
  infer_instance

/-- Every nonempty square minor of a rational rectangular matrix is strictly positive,
with row and column selections taken in their inherited orders. -/
def IsStrictlyTotallyPositive {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ∀ k : Fin (min m n),
    ∀ rows : Fin (k + 1) → Fin m,
      IsIncreasingSelection rows →
        ∀ cols : Fin (k + 1) → Fin n,
          IsIncreasingSelection cols →
            0 < (M.submatrix rows cols).det

instance {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) :
    Decidable (IsStrictlyTotallyPositive M) := by
  unfold IsStrictlyTotallyPositive
  infer_instance

/-- Adjacent increase is equivalent to the standard strict-monotonicity condition. -/
theorem isIncreasingSelection_iff_strictMono {k : ℕ} {α : Type*} [Preorder α]
    (f : Fin (k + 1) → α) : IsIncreasingSelection f ↔ StrictMono f := by
  rw [Fin.strictMono_iff_lt_succ]
  rfl

/-- The four ordered rational support nodes in the packet's counterexample. -/
def rankThreeWitnessNodes : Fin 4 → ℚ := ![(1 : ℚ) / 100, 1, 2, 3]

/-- The four positive rational row weights in the packet's counterexample. -/
def rankThreeWitnessWeights : Fin 4 → ℚ := ![11, 10, (1 : ℚ) / 100, (1 : ℚ) / 100]

/-- The packet's `4 × 6` weighted power matrix. -/
def rankThreeWitnessMatrix : Matrix (Fin 4) (Fin 6) ℚ :=
  fun i j => rankThreeWitnessWeights i * rankThreeWitnessNodes i ^ (j : ℕ)

/-- The exact moment/column-sum sequence of the weighted power matrix. -/
def rankThreeWitnessMoment (j : ℕ) : ℚ :=
  ∑ i : Fin 4, rankThreeWitnessWeights i * rankThreeWitnessNodes i ^ j

/-- Factorial-scaled moments used in the completed Bezout matrix. -/
def rankThreeWitnessScaledMoment (j : ℕ) : ℚ :=
  rankThreeWitnessMoment j / Nat.factorial (2 * j)

/-- The completed Bezout matrix attached to the witness moments. -/
def rankThreeWitnessCompletedBezout (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
    (i + j + 1 - 2 * a : ℕ) * rankThreeWitnessScaledMoment a *
      rankThreeWitnessScaledMoment (i + j + 1 - a)

/-- The packet's rank-two normalized numerator. -/
def rankTwoWitnessNormalizedNumerator : ℚ :=
  3 * rankThreeWitnessMoment 0 * rankThreeWitnessMoment 1 * rankThreeWitnessMoment 3 +
    15 * rankThreeWitnessMoment 1 ^ 2 * rankThreeWitnessMoment 2 -
      10 * rankThreeWitnessMoment 0 * rankThreeWitnessMoment 2 ^ 2

/-- The packet's integer-normalized rank-three completed Bezout numerator. -/
def rankThreeWitnessNormalizedNumerator : ℚ :=
  36578304000 * (rankThreeWitnessCompletedBezout 3).det

/-- The support nodes are strictly ordered and every row weight is positive. -/
theorem rankThreeWitness_parameters :
    IsIncreasingSelection rankThreeWitnessNodes ∧
      ∀ i, 0 < rankThreeWitnessWeights i := by
  native_decide

/-- A `4 × 6` matrix has exactly 209 nonempty square minors. -/
theorem rankThreeWitness_availableMinorCount :
    (∑ k ∈ Finset.range 4, Nat.choose 4 (k + 1) * Nat.choose 6 (k + 1)) = 209 := by
  native_decide

/-- All 209 available minors of the exact weighted power witness are positive. -/
theorem rankThreeWitness_strictlyTotallyPositive :
    IsStrictlyTotallyPositive rankThreeWitnessMatrix := by
  native_decide

/-- The six exact column sums printed in the packet. -/
theorem rankThreeWitness_columnSums :
    (fun j : Fin 6 => rankThreeWitnessMoment j) =
      ![(1051 : ℚ) / 50, (254 : ℚ) / 25, (101311 : ℚ) / 10000,
        (10350011 : ℚ) / 1000000, (1097000011 : ℚ) / 100000000,
        (127500000011 : ℚ) / 10000000000] := by
  native_decide

/-- The exact positive rank-two and negative rank-three normalized numerators. -/
theorem rankTwoPositive_rankThreeNegative_stpWitness :
    rankTwoWitnessNormalizedNumerator = (1858050996109 : ℚ) / 2500000000 ∧
      0 < rankTwoWitnessNormalizedNumerator ∧
    rankThreeWitnessNormalizedNumerator =
      -(4942242941740486966119673885039 : ℚ) / 31250000000000000000000 ∧
      rankThreeWitnessNormalizedNumerator < 0 := by
  native_decide

end MathlibPlus.MomentGeometry
