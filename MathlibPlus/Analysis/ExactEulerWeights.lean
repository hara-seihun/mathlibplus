import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 12712: preserving all prime Euler weights forces the temperature
reparametrization to be the identity on the interval. -/
theorem exactEulerWeights_rigid
    (I : Set ℝ) (_hI : I.Nonempty) (_hIord : I.OrdConnected)
    (β : ℝ → ℝ)
    (hweights : ∀ (p : ℕ), p.Prime → ∀ s ∈ I,
      Real.exp (-β s * Real.log p) = Real.rpow p (-s)) :
    ∀ s ∈ I, β s = s := by
  intro s hs
  have htwo := hweights 2 (by norm_num : Nat.Prime 2) s hs
  change Real.exp (-β s * Real.log (2 : ℝ)) = (2 : ℝ) ^ (-s) at htwo
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at htwo
  have h_exp : -β s * Real.log (2 : ℝ) = Real.log (2 : ℝ) * -s :=
    Real.exp_injective htwo
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

end MathlibPlus.Analysis
