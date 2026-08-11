import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Nat.Cast.Field

open MeasureTheory

namespace MathlibPlus.Analysis.CompleteCellTelescoping

/-- Claim 23781: complete unit cells telescope to one interval. -/
theorem completeCellTelescoping
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N₀ A B N₁ : ℕ)
    (hN : max (max N₀ A) B ≤ N₁)
    {F : ℝ → E}
    (hF : IntervalIntegrable F volume
      (max (max N₀ A) B : ℝ) (N₁ : ℝ)) :
    ∑ N ∈ Finset.Ico (max (max N₀ A) B) N₁,
        ∫ r in (0 : ℝ)..1, F (N + r) =
      ∫ v in (max (max N₀ A) B : ℝ)..(N₁ : ℝ), F v := by
  let b : ℕ := max (max N₀ A) B
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := F) (a := fun k : ℕ => (k : ℝ)) hN
    (fun k hk => by
      have hmem := hk
      have hbk : (max (max N₀ A) B : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast hmem.1
      have hkN : (↑(k + 1) : ℝ) ≤ (N₁ : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hmem.2)
      apply hF.mono_set
      rw [Set.uIcc_of_le (by norm_num),
        Set.uIcc_of_le (by exact_mod_cast hN)]
      exact Set.Icc_subset_Icc hbk hkN)
  have hrewrite (N : ℕ) :
      (∫ r in (0 : ℝ)..1, F (N + r)) =
        ∫ x in (N : ℝ)..(N + 1 : ℕ), F x := by
    rw [intervalIntegral.integral_comp_add_left]
    congr 1 <;> norm_num
  simpa only [hrewrite, Nat.cast_max] using hsum

end MathlibPlus.Analysis.CompleteCellTelescoping
