import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim1788

open scoped BigOperators

/-- The explicit hook determinant sum is strictly positive on the admissible
range `1 ≤ n ≤ d` and `ell < d`; the associated `Z`-factor is positive too.
This is the manifestly-positive formula from claim 1788. -/
theorem manifestlyPositiveHookDeterminantSum_claim1788
    (d n ell : ℕ) (hn : 1 ≤ n) (hnd : n ≤ d) (hell : ell < d) :
    let e := d - ell
    let κ : ℚ :=
      (e : ℚ) * (e + ell + 1) * Nat.choose (e + 2 * ell + 1) ell
    let D : ℚ := κ / (n + ell) *
      (∑ j ∈ Finset.range (ell + 1),
        ((Nat.choose ell j : ℚ) *
          Nat.choose (e - 1) (n - 1 - j)) /
          (e + ell + j + 1))
    0 < D ∧ 0 < ((d + n : ℚ) / e) * D := by
  dsimp
  let e := d - ell
  let κ : ℚ :=
    (e : ℚ) * (e + ell + 1) * Nat.choose (e + 2 * ell + 1) ell
  let f : ℕ → ℚ := fun j =>
    ((Nat.choose ell j : ℚ) * Nat.choose (e - 1) (n - 1 - j)) /
      (e + ell + j + 1)
  have he : 1 ≤ e := by
    dsimp [e]
    omega
  have hne : 0 < (n + ell : ℚ) := by
    positivity
  have hκ : 0 < κ := by
    dsimp [κ]
    have h₁ : 0 < (e : ℚ) := by positivity
    have h₂ : 0 < (e + ell + 1 : ℚ) := by positivity
    have h₃ : 0 < (Nat.choose (e + 2 * ell + 1) ell : ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    positivity
  have hf_nonneg : ∀ j ∈ Finset.range (ell + 1), 0 ≤ f j := by
    intro j hj
    dsimp [f]
    have hden : 0 < (e + ell + j + 1 : ℚ) := by positivity
    have hc₁ : 0 ≤ (Nat.choose ell j : ℚ) := by positivity
    have hc₂ : 0 ≤ (Nat.choose (e - 1) (n - 1 - j) : ℚ) := by positivity
    positivity
  have hf_pos : ∃ j ∈ Finset.range (ell + 1), 0 < f j := by
    by_cases hne' : n ≤ e
    · refine ⟨0, by simp, ?_⟩
      dsimp [f]
      have hc₁ : 0 < (Nat.choose ell 0 : ℚ) := by
        exact_mod_cast Nat.choose_pos (by omega)
      have hc₂ : 0 < (Nat.choose (e - 1) (n - 1) : ℚ) := by
        exact_mod_cast Nat.choose_pos (by omega)
      have hden : 0 < (e + ell + 0 + 1 : ℚ) := by positivity
      positivity
    · have hlt : e < n := by omega
      have hjle : n - e ≤ ell := by omega
      refine ⟨n - e, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · dsimp [f]
        have hc₁ : 0 < (Nat.choose ell (n - e) : ℚ) := by
          exact_mod_cast Nat.choose_pos hjle
        have hc₂ : 0 < (Nat.choose (e - 1) (n - 1 - (n - e)) : ℚ) := by
          have harg : n - 1 - (n - e) = e - 1 := by omega
          rw [harg]
          exact_mod_cast Nat.choose_pos (by omega)
        have hj_nonneg : (0 : ℚ) ≤ ((n - e : ℕ) : ℚ) := by positivity
        have hden : 0 < (e : ℚ) + ell + ((n - e : ℕ) : ℚ) + 1 := by
          positivity
        positivity
  have hsum : 0 < ∑ j ∈ Finset.range (ell + 1), f j :=
    Finset.sum_pos' hf_nonneg hf_pos
  have hD : 0 < κ / (n + ell) * ∑ j ∈ Finset.range (ell + 1), f j := by
    positivity
  have hZ : 0 < ((d + n : ℚ) / e) := by
    have heq : (e : ℚ) > 0 := by positivity
    positivity
  constructor
  · simpa [f] using hD
  · exact mul_pos hZ hD

end MathlibPlus.Combinatorics.Claim1788
