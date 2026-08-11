import Mathlib

namespace MathlibPlus.NumberTheory.Claim16816

/-- The all-shifts statement is exactly the change of variables `m = n - k`;
all endpoint inequalities are retained explicitly. -/
theorem allShifts_iff (n : ℕ) (τ : ℕ → ℕ) :
    (∀ m, 1 ≤ m → m < n → τ m ≤ n - m + 2) ↔
      (∀ k, 1 ≤ k → k < n → τ (n - k) ≤ k + 2) := by
  constructor
  · intro h k hk₁ hkₙ
    have hm₁ : 1 ≤ n - k := by omega
    have hmₙ : n - k < n := by omega
    have hv := h (n - k) hm₁ hmₙ
    have heq : n - (n - k) = k := by omega
    rw [heq] at hv
    exact hv
  · intro h m hm₁ hmₙ
    have hk₁ : 1 ≤ n - m := by omega
    have hkₙ : n - m < n := by omega
    have hv := h (n - m) hk₁ hkₙ
    have heq : n - (n - m) = m := by omega
    rw [heq] at hv
    exact hv

end MathlibPlus.NumberTheory.Claim16816
