import Mathlib.Tactic

namespace MathlibPlus.NumberTheory.Claim57353

theorem only_admissible_solution
    (m γ : ℤ) (hm : 0 < m) (hγ : 0 ≤ γ)
    (h : m * (2 * m * (γ - 1) - 4 * γ + 1) = 3) :
    m = 3 ∧ γ = 3 := by
  have hdiv : m ∣ (3 : ℤ) := by
    refine ⟨2 * m * (γ - 1) - 4 * γ + 1, ?_⟩
    exact h.symm
  have hnat0 : m.natAbs ∣ (3 : ℤ).natAbs :=
    (Int.natAbs_dvd_natAbs).2 hdiv
  have hnat : m.natAbs ∣ 3 := by
    norm_num at hnat0 ⊢
    exact hnat0
  have hcases : m.natAbs = 1 ∨ m.natAbs = 3 := by
    exact (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hnat
  have hm_nonneg : 0 ≤ m := le_of_lt hm
  have hm_abs : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm_nonneg
  rcases hcases with h1 | h3
  · have hm1 : m = 1 := by
      calc
      m = (m.natAbs : ℤ) := hm_abs.symm
      _ = 1 := by exact_mod_cast h1
    subst m
    constructor <;> omega
  · have hm3 : m = 3 := by
      calc
      m = (m.natAbs : ℤ) := hm_abs.symm
      _ = 3 := by exact_mod_cast h3
    subst m
    constructor
    · rfl
    · omega

end MathlibPlus.NumberTheory.Claim57353
