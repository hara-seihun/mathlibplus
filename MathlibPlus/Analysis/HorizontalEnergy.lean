import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim11628

/-- The two displayed coefficient vectors have the same frequency-weighted
energy but different coherent second-derivative traces. -/
theorem horizontalEnergy_not_coherentTraceDetermining :
    let frequencies : Fin 2 → ℝ := ![1, 2]
    let positive : Fin 2 → ℝ := ![1, 1]
    let signed : Fin 2 → ℝ := ![1, -1]
    let energy (c : Fin 2 → ℝ) :=
      ∑ i, (frequencies i) ^ 2 * (c i) ^ 2
    let coherentTrace (c : Fin 2 → ℝ) :=
      ∑ i, (frequencies i) ^ 2 * c i
    energy positive = 5 ∧
      energy signed = 5 ∧
      coherentTrace positive = 5 ∧
      coherentTrace signed = -3 ∧
      coherentTrace positive ≠ coherentTrace signed := by
  dsimp
  norm_num [Fin.sum_univ_two]

end MathlibPlus.Analysis.Claim11628
