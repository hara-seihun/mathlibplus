import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory

/-- Exact first-three Newton-sum identities for the 27 interior gaps and
    the one exterior root `4 + δ`.  The source's root-range hypotheses are
    retained even though the identities are algebraic. -/
theorem claim34997_exactInteriorGapMomentIdentities
    (δ : ℝ) (α : Fin 27 → ℝ)
    (_hδ : 0 < δ ∧ δ < (27 : ℝ) / 1000)
    (_hα : ∀ i, 0 < α i ∧ α i < 4) :
    let ρ := 4 + δ
    let S := ρ + ∑ i : Fin 27, α i
    let p₂ := ρ ^ 2 + ∑ i : Fin 27, (α i) ^ 2
    let p₃ := ρ ^ 3 + ∑ i : Fin 27, (α i) ^ 3
    let Y := ∑ i : Fin 27, (4 - α i)
    let Z := ∑ i : Fin 27, (4 - α i) ^ 2
    let W := ∑ i : Fin 27, (4 - α i) ^ 3
    Y = 112 - S + δ ∧
      Z = 448 - 8 * S + p₂ - δ ^ 2 ∧
      W = 1792 - 48 * S + 12 * p₂ - p₃ + δ ^ 3 := by
  dsimp
  have hsum0 : (∑ _i : Fin 27, (4 : ℝ)) = 108 := by norm_num
  have hsum1 : (∑ i : Fin 27, (4 - α i)) = 108 - ∑ i : Fin 27, α i := by
    rw [Finset.sum_sub_distrib]
    rw [hsum0]
  have hsum2 : (∑ i : Fin 27, (4 - α i) ^ 2) =
      432 - 8 * (∑ i : Fin 27, α i) + ∑ i : Fin 27, (α i) ^ 2 := by
    calc
      (∑ i : Fin 27, (4 - α i) ^ 2) =
          ∑ i : Fin 27, ((16 : ℝ) - 8 * α i + (α i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 432 - 8 * (∑ i : Fin 27, α i) + ∑ i : Fin 27, (α i) ^ 2 := by
            simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            rw [Finset.mul_sum]
            ring
  have hsum3 : (∑ i : Fin 27, (4 - α i) ^ 3) =
      1728 - 48 * (∑ i : Fin 27, α i) + 12 * (∑ i : Fin 27, (α i) ^ 2) -
        ∑ i : Fin 27, (α i) ^ 3 := by
    calc
      (∑ i : Fin 27, (4 - α i) ^ 3) =
          ∑ i : Fin 27, ((64 : ℝ) - 48 * α i + 12 * (α i) ^ 2 - (α i) ^ 3) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 1728 - 48 * (∑ i : Fin 27, α i) + 12 * (∑ i : Fin 27, (α i) ^ 2) -
          ∑ i : Fin 27, (α i) ^ 3 := by
            simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            rw [Finset.mul_sum, Finset.mul_sum]
            ring
  rw [hsum1, hsum2, hsum3]
  constructor
  · ring
  constructor <;> ring

end MathlibPlus.NumberTheory
