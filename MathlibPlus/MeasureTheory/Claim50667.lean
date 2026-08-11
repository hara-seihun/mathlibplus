import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.MeasureTheory.Claim50667

/-- The four-atom covariance table and its uniform average have the exact
values recorded in claim 50667. -/
theorem fourAtom_averageVariance_claim50667 :
    let cov : Fin 4 → Fin 4 → ℚ :=
      fun i j => if i = j then 1 else (7 : ℚ) / 16
    (∀ i, cov i i = 1) ∧
      (∀ i j, i ≠ j → cov i j = (7 : ℚ) / 16) ∧
      (4 * ((1 : ℚ) / 4) ^ 2 +
          12 * ((1 : ℚ) / 4) ^ 2 * ((7 : ℚ) / 16)) = (37 : ℚ) / 64 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp
  · intro i j hij
    simp [hij]
  · norm_num

end MathlibPlus.MeasureTheory.Claim50667
