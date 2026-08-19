import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

open scoped ContDiff

/-- Claim 2462: a packet supported on `(1,B)` becomes an even packet in the
first sampled cell after the scaling `v ↦ c |v|`. -/
theorem firstSampledCellPacket
    (B c δ : ℝ) (φ : ℝ → ℝ)
    (hB1 : 1 < B) (hB2 : B < 2) (hc : B < c)
    (_hφsmooth : ContDiff ℝ ∞ φ)
    (_hφcompact : HasCompactSupport φ)
    (hsupp : Function.support φ ⊆ Set.Ioo 1 B) :
    let p : ℝ → ℝ := fun v => δ * Real.sqrt c * φ (c * |v|)
    HasCompactSupport p ∧
      (∀ v : ℝ, p (-v) = p v) ∧
      Function.support p ⊆ {v | 1 / c < |v| ∧ |v| < B / c} ∧
      Function.support p ⊆ {v | |v| < 2 / c} := by
  dsimp
  have hcpos : 0 < c := by linarith
  have hcell : ∀ v, v ∈ Function.support (fun v : ℝ =>
      δ * Real.sqrt c * φ (c * |v|)) →
      1 / c < |v| ∧ |v| < B / c := by
    intro v hv
    have hφ : φ (c * |v|) ≠ 0 := by
      intro hz
      apply Function.mem_support.mp hv
      simp [hz]
    have hφ' := hsupp (Function.mem_support.mpr hφ)
    have hlo : 1 < c * |v| := hφ'.1
    have hhi : c * |v| < B := hφ'.2
    constructor
    · apply (div_lt_iff₀ hcpos).2
      nlinarith
    · apply (lt_div_iff₀ hcpos).2
      nlinarith
  have hpcompact : HasCompactSupport (fun v : ℝ =>
      δ * Real.sqrt c * φ (c * |v|)) := by
    apply HasCompactSupport.intro (isCompact_Icc :
      IsCompact (Set.Icc (-(B / c)) (B / c)))
    intro v hv
    by_contra hp
    have hv' := hcell v (Function.mem_support.mpr hp)
    have habs : |v| ≤ B / c := le_of_lt hv'.2
    have hvK : v ∈ Set.Icc (-(B / c)) (B / c) := (abs_le.mp habs)
    exact hv hvK
  refine ⟨hpcompact, ?_, hcell, ?_⟩
  · intro v
    simp [abs_neg]
  · intro v hv
    have hupper := (hcell v hv).2
    apply (lt_div_iff₀ hcpos).2
    exact lt_trans ((lt_div_iff₀ hcpos).1 hupper) hB2

end

end MathlibPlus.Analysis
