import Mathlib

namespace MathlibPlus.Algebra.Claim1748

/--
The source's `Z_(n,k)` is not defined in the standalone claim. This theorem
formalizes the displayed normalized right-hand side and the asserted
positivity of all of its factors, leaving that external normalization as a
fidelity boundary.
-/
theorem positive_amplitude_ratio_factors
    (n k d : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hd : max n (k + 1) ≤ d) :
    0 < (d + k - 1 : ℝ) ∧
      0 < (n - k + 1 : ℝ) ∧
      0 < (d : ℝ) ^ 2 + d - k * (n + 1) ∧
      0 < (k : ℝ) * d * (d - 1) * (n + 1) ∧
      0 < (Nat.choose d (k - 1) : ℝ) ∧
      0 <
        (((d + k - 1 : ℝ) * (n - k + 1) *
            ((d : ℝ) ^ 2 + d - k * (n + 1))) /
          ((k : ℝ) * d * (d - 1) * (n + 1))) *
          (Nat.choose d (k - 1) : ℝ) := by
  have hdn : (n : ℝ) ≤ d := by
    exact_mod_cast le_trans (Nat.le_max_left n (k + 1)) hd
  have hdk1 : (k + 1 : ℝ) ≤ d := by
    exact_mod_cast le_trans (Nat.le_max_right n (k + 1)) hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hdk : (k : ℝ) ≤ d := by nlinarith
  have hdn0 : (0 : ℝ) ≤ d - n := by linarith
  have hdk0 : (0 : ℝ) ≤ d - k := by linarith
  have hdkpos : (0 : ℝ) < d - k := by linarith
  have hthird : (0 : ℝ) < (d : ℝ) ^ 2 + d - k * (n + 1) := by
    have h₁ : 0 ≤ (d : ℝ) * (d - n) := mul_nonneg hdR hdn0
    have h₂ : 0 ≤ (n : ℝ) * (d - k) := mul_nonneg (by positivity) hdk0
    nlinarith
  have hfirst : (0 : ℝ) < (d + k - 1 : ℝ) := by
    norm_num
    nlinarith
  have hsecond : (0 : ℝ) < (n - k + 1 : ℝ) := by
    have hsecondNat : 0 < n - k + 1 := Nat.zero_lt_succ _
    exact_mod_cast hsecondNat
  have hden : (0 : ℝ) < (k : ℝ) * d * (d - 1) * (n + 1) := by
    have hd2 : (1 : ℝ) < d := by nlinarith [hkR, hdk1]
    positivity
  have hchooseNat : 0 < Nat.choose d (k - 1) := by
    apply Nat.choose_pos
    omega
  have hchoose : (0 : ℝ) < (Nat.choose d (k - 1) : ℝ) := by
    exact_mod_cast hchooseNat
  refine ⟨hfirst, hsecond, hthird, hden, hchoose, ?_⟩
  exact mul_pos (div_pos (mul_pos (mul_pos hfirst hsecond) hthird) hden) hchoose

theorem positive_amplitude_ratio
    (n k d : ℕ) (z₀ zₖ : ℝ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hd : max n (k + 1) ≤ d)
    (h_ratio : zₖ / z₀ =
      (((d + k - 1 : ℝ) * (n - k + 1) *
          ((d : ℝ) ^ 2 + d - k * (n + 1))) /
        ((k : ℝ) * d * (d - 1) * (n + 1))) *
        (Nat.choose d (k - 1) : ℝ)) :
    0 < zₖ / z₀ := by
  have hpos := positive_amplitude_ratio_factors n k d hk hkn hd
  rw [h_ratio]
  exact hpos.2.2.2.2.2

end MathlibPlus.Algebra.Claim1748
