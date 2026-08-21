-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.MomentGeometry.AlgebraicWitnesses
import MathlibPlus.MomentGeometry.RankThreeCounterexample

namespace MathlibPlus.MomentGeometry

open Matrix
open scoped BigOperators

/-- Exact finite witness for the smaller three-atom exterior-positive no-go. -/
theorem claim10599_smallerThreeAtomWitness :
    let nodes : Fin 3 → ℚ := ![(1 : ℚ), 2, 6]
    let weights : Fin 3 → ℚ := ![1, 1, 5]
    let B : Matrix (Fin 3) (Fin 4) ℚ :=
      fun i j => weights i * nodes i ^ (j : ℕ)
    IsStrictlyTotallyPositive B ∧
      (∑ k ∈ Finset.range 3, Nat.choose 3 (k + 1) * Nat.choose 4 (k + 1)) = 34 ∧
      (fun j : Fin 4 => ∑ i : Fin 3, B i j) = ![(7 : ℚ), 33, 185, 1089] ∧
      rankTwoColumnSumExpression 7 33 185 1089 = -15106 := by
  dsimp
  constructor
  · unfold IsStrictlyTotallyPositive IsIncreasingSelection
    native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · norm_num [rankTwoColumnSumExpression]

/-- The matrix-level exterior-positive observable obstruction at the exact witness. -/
theorem claim10599_exteriorPositiveNoGo :
    ¬ (∃ Φ : Matrix (Fin 3) (Fin 4) ℚ → ℚ,
      (∀ M, IsStrictlyTotallyPositive M → 0 ≤ Φ M) ∧
      (∀ M, IsStrictlyTotallyPositive M →
        Φ M = rankTwoColumnSumExpression
          (∑ i : Fin 3, M i 0) (∑ i : Fin 3, M i 1)
          (∑ i : Fin 3, M i 2) (∑ i : Fin 3, M i 3))) := by
  intro h
  rcases h with ⟨Φ, hnonneg, heq⟩
  let nodes : Fin 3 → ℚ := ![(1 : ℚ), 2, 6]
  let weights : Fin 3 → ℚ := ![1, 1, 5]
  let B : Matrix (Fin 3) (Fin 4) ℚ :=
    fun i j => weights i * nodes i ^ (j : ℕ)
  have hB : IsStrictlyTotallyPositive B := by
    unfold IsStrictlyTotallyPositive IsIncreasingSelection
    native_decide
  have hpos : 0 ≤ Φ B := hnonneg B hB
  have heqB := heq B hB
  have h0 : (∑ i : Fin 3, B i 0) = (7 : ℚ) := by native_decide
  have h1 : (∑ i : Fin 3, B i 1) = (33 : ℚ) := by native_decide
  have h2 : (∑ i : Fin 3, B i 2) = (185 : ℚ) := by native_decide
  have h3 : (∑ i : Fin 3, B i 3) = (1089 : ℚ) := by native_decide
  have h0R : (∑ i : Fin 3, (B i 0 : ℝ)) = 7 := by exact_mod_cast h0
  have h1R : (∑ i : Fin 3, (B i 1 : ℝ)) = 33 := by exact_mod_cast h1
  have h2R : (∑ i : Fin 3, (B i 2 : ℝ)) = 185 := by exact_mod_cast h2
  have h3R : (∑ i : Fin 3, (B i 3 : ℝ)) = 1089 := by exact_mod_cast h3
  rw [h0R, h1R, h2R, h3R] at heqB
  have hneg : (Φ B : ℝ) < 0 := by
    rw [heqB]
    norm_num [rankTwoColumnSumExpression]
  have hposR : (0 : ℝ) ≤ Φ B := by exact_mod_cast hpos
  linarith

end MathlibPlus.MomentGeometry
