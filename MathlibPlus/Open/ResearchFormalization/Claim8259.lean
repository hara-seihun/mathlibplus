import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

open scoped BigOperators

/-- Claim 8259: the depth and prime-power majorants are summable. -/
def packetMajorantSummabilityClaim8259 : Prop :=
  let depthTerm : ℝ → ℝ → ℕ → ℝ := fun c L a ↦
    if 1 ≤ a then
      Real.exp (-c * Real.sqrt ((a : ℝ) * L))
    else 0
  let primePowerMajorant : ℝ → ℝ → ℕ → ℕ → ℝ := fun C c q a ↦
    if Nat.Prime q ∧ 1 ≤ a then
      C * (Real.log (q : ℝ) / (q : ℝ)) *
        Real.exp (-c * Real.sqrt ((a : ℝ) * Real.log (q : ℝ)))
    else 0
  ∀ c C : ℝ, 0 < c → 0 < C →
    (∃ K : ℝ, 0 < K ∧
      ∀ q : ℕ, Nat.Prime q →
        (∑' a : ℕ, depthTerm c (Real.log (q : ℝ)) a) ≤
          K * (1 + (Real.sqrt (Real.log (q : ℝ)))⁻¹) *
            Real.exp (-c * Real.sqrt (Real.log (q : ℝ)))) ∧
    Summable (fun n : ℕ ↦
      if 2 ≤ n then
        (Real.log (n : ℝ) / (n : ℝ)) *
          Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))
      else 0) ∧
    Summable (fun qa : ℕ × ℕ ↦
      primePowerMajorant C c qa.1 qa.2)

end

end MathlibPlus.Open.ResearchFormalization
