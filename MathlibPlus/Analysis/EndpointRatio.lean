import Mathlib

namespace MathlibPlus.Analysis.EndpointRatio

/-- Claim 3033: positivity and log-concavity make the first adjacent ratio dominate
all later ratios; the bound `h₁ < 4` gives the displayed final inequality. -/
theorem endpoint_ratio_dominance
    (Δ : ℕ → ℝ) (h₁ : ℝ) (m : ℕ)
    (hpos : ∀ n : ℕ, 0 < Δ n)
    (hlog : ∀ n : ℕ, Δ (n + 1) ^ 2 ≥ Δ n * Δ (n + 2))
    (hfirst : Δ 1 / Δ 0 ≤ h₁)
    (hh₁ : h₁ < 4) :
    0 < Δ (m + 1) / Δ m ∧
      Δ (m + 1) / Δ m ≤ Δ 1 / Δ 0 ∧
      Δ 1 / Δ 0 ≤ h₁ ∧ h₁ < 4 ∧
      (1 / 4 : ℝ) * Δ (m + 1) < Δ m := by
  have hratio : ∀ n : ℕ, 0 < n →
      Δ (n + 1) / Δ n ≤ Δ n / Δ (n - 1) := by
    intro n hn
    have hnpos : 0 < Δ n := hpos n
    have hnprev : 0 < Δ (n - 1) := hpos (n - 1)
    have hlogn := hlog (n - 1)
    have hsucc : n - 1 + 1 = n := by omega
    have hnext : n - 1 + 2 = n + 1 := by omega
    rw [hsucc, hnext] at hlogn
    apply (div_le_div_iff₀ hnpos hnprev).2
    nlinarith [hlogn]
  have hdom : ∀ k : ℕ, Δ (k + 1) / Δ k ≤ Δ 1 / Δ 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        Δ (k + 1 + 1) / Δ (k + 1) ≤ Δ (k + 1) / Δ k := by
          exact hratio (k + 1) (by omega)
        _ ≤ Δ 1 / Δ 0 := ih
  have hpositive : 0 < Δ (m + 1) / Δ m := div_pos (hpos _) (hpos _)
  have hfinal : (1 / 4 : ℝ) * Δ (m + 1) < Δ m := by
    have hm : 0 < Δ m := hpos m
    have hratio_lt : Δ (m + 1) / Δ m < 4 :=
      lt_of_le_of_lt (le_trans (hdom m) hfirst) hh₁
    have hclear : Δ (m + 1) < 4 * Δ m := (div_lt_iff₀ hm).mp hratio_lt
    nlinarith
  exact ⟨hpositive, hdom m, hfirst, hh₁, hfinal⟩

end MathlibPlus.Analysis.EndpointRatio
