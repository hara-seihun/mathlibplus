import Mathlib

namespace MathlibPlus.Combinatorics.Claim40389

/--
An abstract induction form of the restricted-class argument in claim 40389.
A nonterminal rank-`r` family is reduced to a transformed family of rank
`r - p + 1`, with the collision-energy estimate `K^p`; the transformed family
is quantified in the same class, so the induction hypothesis applies to it.
-/
theorem arbitraryDepthRestrictedClassBound_claim40389
    {Family : ℕ → Type*}
    (size : {r : ℕ} → Family r → ℕ)
    (terminal : {r : ℕ} → Family r → Prop)
    {K C B : ℝ}
    (hK : 1 ≤ K)
    (hC : 1 ≤ C)
    (hB : max C (K ^ 2) ≤ B)
    (h_terminal : ∀ {r : ℕ} (F : Family r), terminal F →
      (size F : ℝ) ≤ C ^ r)
    (h_nonterminal : ∀ {r : ℕ} (F : Family r), ¬ terminal F →
      ∃ (p : ℕ) (G : Family (r - p + 1)),
        2 ≤ p ∧ p ≤ r ∧ (size F : ℝ) ≤ K ^ p * size G) :
    ∀ {r : ℕ} (F : Family r), (size F : ℝ) ≤ B ^ r := by
  have hCB : C ≤ B := le_trans (le_max_left _ _) hB
  have hB1 : 1 ≤ B := le_trans hC hCB
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hKsq : K ^ 2 ≤ B := le_trans (le_max_right _ _) hB
  have hKleSq : K ≤ K ^ 2 := by
    nlinarith [hK]
  have hKB : K ≤ B := le_trans hKleSq hKsq
  have hpow_mono : ∀ q : ℕ, K ^ q ≤ B ^ q := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hKB hK0 (pow_nonneg hB0 _)
  have hpow : ∀ p : ℕ, 2 ≤ p → K ^ p ≤ B ^ (p - 1) := by
    intro p hp
    let q := p - 2
    have hpq : p = 2 + q := by
      dsimp [q]
      omega
    calc
      K ^ p = K ^ 2 * K ^ q := by rw [hpq, pow_add]
      _ ≤ B * B ^ q := by
        apply mul_le_mul
        · exact hKsq
        · exact hpow_mono q
        · exact pow_nonneg hK0 _
        · exact hB0
      _ = B ^ (p - 1) := by
        rw [show p - 1 = q + 1 by omega, pow_succ]
        ring
  have hpow_CB : ∀ q : ℕ, C ^ q ≤ B ^ q := by
    intro q
    exact pow_le_pow_left₀ (le_trans (by norm_num) hC) hCB q
  intro r F
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases ht : terminal F
      · calc
          (size F : ℝ) ≤ C ^ r := h_terminal F ht
          _ ≤ B ^ r := hpow_CB r
      · obtain ⟨p, G, hp2, hpr, hbound⟩ := h_nonterminal F ht
        have htail : r - p + 1 < r := by omega
        calc
          (size F : ℝ) ≤ K ^ p * size G := hbound
          _ ≤ K ^ p * B ^ (r - p + 1) := by
            apply mul_le_mul_of_nonneg_left (ih (r - p + 1) htail G)
            exact pow_nonneg hK0 _
          _ ≤ B ^ (p - 1) * B ^ (r - p + 1) := by
            apply mul_le_mul_of_nonneg_right (hpow p hp2)
            exact pow_nonneg hB0 _
          _ = B ^ r := by
            rw [← pow_add]
            congr 1
            omega

end MathlibPlus.Combinatorics.Claim40389
