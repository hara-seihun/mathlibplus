import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 42854: the paired vertical factors vanish at the displayed points. -/
theorem exactZeros_claim42854 (R : ℝ) (hR : R ≠ 0) :
    (let P : ℂ → ℂ := fun z => 1 + (z / (R : ℂ)) ^ 2;
     P (Complex.I * (R : ℂ)) = 0 ∧
       P (-Complex.I * (R : ℂ)) = 0) := by
  dsimp
  constructor <;> field_simp [hR] <;> simp [Complex.I_sq]

/-- Claim 42856: the quadratic factor is uniformly close to one on a disk. -/
theorem uniformDiskEstimate_claim42856 (R B : ℝ) (hR : 0 < R)
    (z : ℂ) (hz : ‖z‖ ≤ B) :
    ‖(1 + (z / (R : ℂ)) ^ 2) - 1‖ ≤ (B / R) ^ 2 := by
  have hB : 0 ≤ B := by
    exact le_trans (norm_nonneg z) hz
  have hnormR : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  calc
    ‖(1 + (z / (R : ℂ)) ^ 2) - 1‖ = ‖(z / (R : ℂ)) ^ 2‖ := by ring_nf
    _ = ‖z / (R : ℂ)‖ ^ 2 := by rw [norm_pow]
    _ = (‖z‖ / R) ^ 2 := by rw [norm_div, hnormR]
    _ ≤ (B / R) ^ 2 := by
      gcongr
    _ = (B / R) ^ 2 := rfl

/-- Claim 42857: the factors converge uniformly to one on each fixed disk. -/
theorem compactOpenConvergence_claim42857 :
    ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ R₀ : ℝ, 0 < R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          ∀ z : ℂ, ‖z‖ ≤ B →
            ‖(1 + (z / (R : ℂ)) ^ 2) - 1‖ ≤ ε := by
  intro B ε hB hε
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  let R₀ : ℝ := max 1 (B / Real.sqrt ε)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR z hz
  have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR
  have hRlower : B / Real.sqrt ε ≤ R := le_trans (le_max_right _ _) hR
  have hprod : B ≤ R * Real.sqrt ε := (div_le_iff₀ hsqrt).mp hRlower
  have hratio : B / R ≤ Real.sqrt ε := by
    apply (div_le_iff₀ hRpos).2
    nlinarith [hprod]
  have hsq : (B / R) ^ 2 ≤ ε := by
    have hnonneg : 0 ≤ B / R := div_nonneg hB (le_of_lt hRpos)
    have hsnonneg : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (le_of_lt hε)]
  exact (uniformDiskEstimate_claim42856 R B hRpos z hz).trans hsq

end MathlibPlus.Analysis
