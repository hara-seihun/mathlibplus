import Mathlib

namespace MathlibPlus.GroupTheory.Claim5845

/--
Claim 5845.  The decisive orbit-size inequality used in the product-wreath
argument is strict for every `m ≥ 3` and `s ≥ 2`.
-/
theorem orbitSize_lt_power
    (m s : ℕ) (hm : 3 ≤ m) (hs : 2 ≤ s) :
    s < m ^ (s - 1) := by
  have hstrong : ∀ n : ℕ, 1 ≤ n → n + 1 < m ^ n := by
    intro n
    induction n with
    | zero =>
        intro hn
        omega
    | succ n ih =>
        intro hn
        by_cases hn0 : n = 0
        · simp [hn0]
          omega
        · have hn_pos : 1 ≤ n := by omega
          have hi := ih hn_pos
          rw [pow_succ]
          have hpow_nonneg : 0 ≤ m ^ n := Nat.zero_le _
          nlinarith
  have hs_pos : 1 ≤ s := by omega
  have h := hstrong (s - 1) (by omega)
  have hsub : (s - 1) + 1 = s := by omega
  simpa [hsub] using h

end MathlibPlus.GroupTheory.Claim5845
