import Mathlib

namespace MathlibPlus.Algebra.Claim24508

/-- The strict second Newton-moment lower bound for the one-exterior
configuration with one root `4 + δ` and 27 roots in `(0, 4)`. -/
theorem strictSecondNewtonMomentLowerBound_claim24508
    (δ : ℝ) (α : Fin 27 → ℝ)
    (hδ : 0 < δ ∧ δ < (27 : ℝ) / 1000)
    (hα : ∀ i, 0 < α i ∧ α i < 4) :
    let S : ℝ := (4 + δ) + ∑ i : Fin 27, α i
    let p₂ : ℝ := (4 + δ) ^ 2 + ∑ i : Fin 27, (α i) ^ 2
    p₂ > -448 + 8 * S + (112 - S) ^ 2 / 27 := by
  dsimp
  let y : Fin 27 → ℝ := fun i => 4 - α i
  have hypos : ∀ i, 0 < y i := by
    intro i
    dsimp [y]
    linarith [(hα i).2]
  have hsum_sq :=
    sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 27)))
      (f := y)
  have hsum_sq' :
      (∑ i : Fin 27, y i) ^ 2 ≤ 27 * ∑ i : Fin 27, (y i) ^ 2 := by
    simpa using hsum_sq
  have hsum_pos : 0 < ∑ i : Fin 27, y i := by
    exact Finset.sum_pos (fun i hi => hypos i) (by simp)
  have hdelta : 0 < δ := hδ.1
  have hsum1 : ∑ i : Fin 27, y i = 108 - ∑ i : Fin 27, α i := by
    dsimp [y]
    rw [Finset.sum_sub_distrib]
    have hconst : (∑ _i : Fin 27, (4 : ℝ)) = 108 := by norm_num
    rw [hconst]
  have hsum2 : ∑ i : Fin 27, (y i) ^ 2 =
      432 - 8 * (∑ i : Fin 27, α i) + ∑ i : Fin 27, (α i) ^ 2 := by
    dsimp [y]
    calc
      (∑ i : Fin 27, (4 - α i) ^ 2) =
          ∑ i : Fin 27, ((16 : ℝ) - 8 * α i + (α i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 432 - 8 * (∑ i : Fin 27, α i) + ∑ i : Fin 27, (α i) ^ 2 := by
            simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            rw [Finset.mul_sum]
            norm_num
  have hgap : 0 < δ ^ 2 + ∑ i : Fin 27, (y i) ^ 2 -
      (∑ i : Fin 27, y i - δ) ^ 2 / 27 := by
    have hbound :
        (∑ i : Fin 27, y i - δ) ^ 2 / 27 ≤
          (∑ i : Fin 27, y i) ^ 2 / 27 + δ ^ 2 / 27 := by
      have hcross : 0 ≤ 2 * δ * ∑ i : Fin 27, y i := by positivity
      have hid :
          (∑ i : Fin 27, y i - δ) ^ 2 =
            (∑ i : Fin 27, y i) ^ 2 -
              2 * δ * ∑ i : Fin 27, y i + δ ^ 2 := by ring
      rw [hid]
      nlinarith
    nlinarith [hsum_sq']
  have hrewrite :
      (4 + δ) ^ 2 + ∑ i : Fin 27, (α i) ^ 2 -
        (-448 + 8 * ((4 + δ) + ∑ i : Fin 27, α i) +
          (112 - ((4 + δ) + ∑ i : Fin 27, α i)) ^ 2 / 27) =
        δ ^ 2 + ∑ i : Fin 27, (y i) ^ 2 -
          (∑ i : Fin 27, y i - δ) ^ 2 / 27 := by
    rw [hsum1, hsum2]
    ring
  have hdiff : 0 <
      (4 + δ) ^ 2 + ∑ i : Fin 27, (α i) ^ 2 -
        (-448 + 8 * ((4 + δ) + ∑ i : Fin 27, α i) +
          (112 - ((4 + δ) + ∑ i : Fin 27, α i)) ^ 2 / 27) := by
    rw [hrewrite]
    exact hgap
  linarith

end MathlibPlus.Algebra.Claim24508
