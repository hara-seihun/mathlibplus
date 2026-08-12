import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace MathlibPlus.Analysis.Claim13803

noncomputable section

open Filter Topology
open Asymptotics

/-- The concrete witness from claim 13803 decays to zero while satisfying both
its decaying and growing power envelopes.  Real powers use `Real.rpow`. -/
theorem explicitCompatibleDecayingWitness :
    let δ : ℝ := 1 / 2
    let η : ℝ := 3 / 4
    let f : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ))
    δ = 1 / 2 ∧
      η = 3 / 4 ∧
      Tendsto f atTop (𝓝 0) ∧
      f =O[atTop] (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) ∧
      f =O[atTop] (fun u : ℝ => u ^ (3 / 4 : ℝ)) := by
  dsimp
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact tendsto_rpow_neg_atTop (by norm_num)
  · exact Asymptotics.isBigO_refl _ _
  · refine (Asymptotics.IsBigOWith.of_bound (c := 1) ?_).isBigO
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hpow : u ^ (-(1 / 2 : ℝ)) ≤ u ^ (3 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hu
      norm_num
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (le_trans (by norm_num) hu) _),
      abs_of_nonneg (Real.rpow_nonneg (le_trans (by norm_num) hu) _)]
    simpa using hpow

end
end MathlibPlus.Analysis.Claim13803
