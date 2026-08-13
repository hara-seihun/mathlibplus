import Mathlib

namespace MathlibPlus.Analysis.Claim1143

/-- Exact denominator-positive reformulation from claim 1143. -/
theorem denominatorPositive_reformulation_claim1143
    {x c : ℝ}
    (hp : 0 < (Nat.primeCounting ⌊x⌋₊ : ℝ))
    (hc : c < Real.log x) :
    0 < Real.log x - c ∧
      ((Nat.primeCounting ⌊x⌋₊ : ℝ) < x / (Real.log x - c) ↔
        Real.log x - x / (Nat.primeCounting ⌊x⌋₊ : ℝ) < c) := by
  let p : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ)
  have hp' : 0 < p := hp
  have hd : 0 < Real.log x - c := sub_pos.mpr hc
  change 0 < Real.log x - c ∧
    (p < x / (Real.log x - c) ↔ Real.log x - x / p < c)
  constructor
  · exact hd
  · constructor
    · intro h
      have h1 : p * (Real.log x - c) < x :=
        (lt_div_iff₀ hd).mp h
      have h2 : (Real.log x - c) * p < x := by
        simpa [mul_comm] using h1
      have h3 : Real.log x - c < x / p :=
        (lt_div_iff₀ hp').2 h2
      linarith
    · intro h
      have h3 : Real.log x - c < x / p := by linarith
      have h2 : (Real.log x - c) * p < x :=
        (lt_div_iff₀ hp').1 h3
      have h1 : p * (Real.log x - c) < x := by
        simpa [mul_comm] using h2
      exact (lt_div_iff₀ hd).2 h1

end MathlibPlus.Analysis.Claim1143
