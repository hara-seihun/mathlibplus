import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace MathlibPlus.Algebra.Claim24474

/-- The first three moments of the 27 interior gaps after separating the root
`4 + δ`, with the source's positivity/support hypotheses retained. -/
theorem interiorGapMomentIdentities
    (δ : ℝ) (α : Fin 27 → ℝ)
    (_hδ : 0 < δ) (_hα : ∀ i, 0 < α i ∧ α i < 4) :
    let S : ℝ := (4 + δ) + ∑ i : Fin 27, α i
    let p₂ : ℝ := (4 + δ) ^ 2 + ∑ i : Fin 27, (α i) ^ 2
    let p₃ : ℝ := (4 + δ) ^ 3 + ∑ i : Fin 27, (α i) ^ 3
    let Y : ℝ := ∑ i : Fin 27, (4 - α i)
    let Z : ℝ := ∑ i : Fin 27, (4 - α i) ^ 2
    let W : ℝ := ∑ i : Fin 27, (4 - α i) ^ 3
    Y = 112 - S + δ ∧
      Z = 448 - 8 * S + p₂ - δ ^ 2 ∧
      W = 1792 - 48 * S + 12 * p₂ - p₃ + δ ^ 3 := by
  dsimp
  have hY : (∑ i : Fin 27, (4 - α i)) =
      (27 : ℝ) * 4 - ∑ i : Fin 27, α i := by
    rw [Finset.sum_sub_distrib]
    simp
  have hZ : (∑ i : Fin 27, (4 - α i) ^ 2) =
      (27 : ℝ) * 16 - 8 * (∑ i : Fin 27, α i) +
        ∑ i : Fin 27, (α i) ^ 2 := by
    calc
      (∑ i : Fin 27, (4 - α i) ^ 2) =
          ∑ i : Fin 27, (16 - 8 * α i + (α i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin 27, (16 - 8 * α i)) +
          ∑ i : Fin 27, (α i) ^ 2 := by
            rw [Finset.sum_add_distrib]
      _ = (27 : ℝ) * 16 - 8 * (∑ i : Fin 27, α i) +
          ∑ i : Fin 27, (α i) ^ 2 := by
            rw [Finset.sum_sub_distrib]
            simp [Finset.sum_mul]
            rw [← Finset.mul_sum]
  have hW : (∑ i : Fin 27, (4 - α i) ^ 3) =
      (27 : ℝ) * 64 - 48 * (∑ i : Fin 27, α i) +
        12 * (∑ i : Fin 27, (α i) ^ 2) -
        ∑ i : Fin 27, (α i) ^ 3 := by
    calc
      (∑ i : Fin 27, (4 - α i) ^ 3) =
          ∑ i : Fin 27, (64 - 48 * α i + 12 * (α i) ^ 2 - (α i) ^ 3) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin 27, (64 - 48 * α i + 12 * (α i) ^ 2)) -
          ∑ i : Fin 27, (α i) ^ 3 := by
            rw [Finset.sum_sub_distrib]
      _ = ((∑ i : Fin 27, (64 - 48 * α i)) +
            ∑ i : Fin 27, 12 * (α i) ^ 2) -
          ∑ i : Fin 27, (α i) ^ 3 := by
            rw [show (fun i : Fin 27 => 64 - 48 * α i + 12 * (α i) ^ 2) =
              (fun i => (64 - 48 * α i) + 12 * (α i) ^ 2) by funext i; rfl,
              Finset.sum_add_distrib]
      _ = (27 : ℝ) * 64 - 48 * (∑ i : Fin 27, α i) +
          12 * (∑ i : Fin 27, (α i) ^ 2) -
          ∑ i : Fin 27, (α i) ^ 3 := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            simp
            rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine ⟨?_, ?_, ?_⟩
  · rw [hY]
    ring
  · rw [hZ]
    ring
  · rw [hW]
    ring

end MathlibPlus.Algebra.Claim24474
