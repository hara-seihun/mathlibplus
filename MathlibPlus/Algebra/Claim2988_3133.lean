import Mathlib

namespace MathlibPlus.Algebra.Claim2988

/-- Positive log-concavity makes the adjacent ratios nonincreasing. -/
theorem adjacentCofactorRatio_le_first_claim2988
    (Δ : ℕ → ℝ) (r : ℕ)
    (hpos : ∀ n, n ≤ r → 0 < Δ n)
    (hlog : ∀ n, 0 < n → n + 1 ≤ r →
      Δ (n - 1) * Δ (n + 1) ≤ Δ n * Δ n) :
    ∀ m, m < r → Δ (m + 1) / Δ m ≤ Δ 1 / Δ 0 := by
  intro m
  induction m with
  | zero =>
      intro _
      simp
  | succ m ih =>
      intro hm
      have hstep : Δ (m + 2) / Δ (m + 1) ≤ Δ (m + 1) / Δ m := by
        apply (div_le_div_iff₀ (hpos (m + 1) (by omega))
          (hpos m (by omega))).2
        simpa [mul_comm] using hlog (m + 1) (by omega) (by omega)
      exact hstep.trans (ih (by omega))

end MathlibPlus.Algebra.Claim2988

namespace MathlibPlus.Algebra.Claim3133

/-- The first Radau identities add the upper bound by the first coefficient. -/
theorem uniformAdjacentCofactorRatio_claim3133
    (Δ : ℕ → ℝ) (r : ℕ)
    (hpos : ∀ n, n ≤ r → 0 < Δ n)
    (hlog : ∀ n, 0 < n → n + 1 ≤ r →
      Δ (n - 1) * Δ (n + 1) ≤ Δ n * Δ n)
    (R₀ R₁ h₁ : ℝ)
    (hR₀ : 0 < R₀) (hR₁ : 0 ≤ R₁)
    (hΔ₀ : Δ 0 = R₀)
    (hΔ₁ : Δ 1 = R₀ * h₁ - R₁) :
    ∀ m, m < r →
      0 < Δ (m + 1) / Δ m ∧
        Δ (m + 1) / Δ m ≤ Δ 1 / Δ 0 ∧
          Δ 1 / Δ 0 ≤ h₁ := by
  have hfirst : Δ 1 / Δ 0 ≤ h₁ := by
    rw [hΔ₀, hΔ₁]
    apply (div_le_iff₀ hR₀).2
    calc
      R₀ * h₁ - R₁ ≤ R₀ * h₁ := by linarith
      _ = h₁ * R₀ := by ring
  intro m hm
  refine ⟨div_pos (hpos (m + 1) (by omega)) (hpos m (by omega)), ?_, hfirst⟩
  exact MathlibPlus.Algebra.Claim2988.adjacentCofactorRatio_le_first_claim2988 Δ r hpos hlog m hm

end MathlibPlus.Algebra.Claim3133
