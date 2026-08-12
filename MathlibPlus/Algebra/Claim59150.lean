import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 59150.  The source's pruning products are represented by their natural
weighted degrees.  The two source facts needed by the arithmetic corollary,
`κ ≤ n` and evenness in the bicentroid case, are explicit hypotheses. -/
theorem strictMajorityResidualWeight_claim59150
    (n κ c D : ℕ)
    (hκ : κ = 1 ∨ κ = 2)
    (hD : (n + 1) / 2 ≤ D)
    (hsum : c + D = n - κ)
    (hκle : κ ≤ n)
    (hκ2even : κ = 2 → Even n) :
    D > c ∧
      (κ = 1 → Even n → D - c ≥ 1) ∧
      (κ = 1 → Odd n → D - c ≥ 2) ∧
      (κ = 2 → D - c ≥ 2) := by
  have hD2 : n + 1 ≤ D * 2 + 2 - 1 :=
    (Nat.div_le_iff_le_mul (by omega : 0 < 2)).mp hD
  rcases hκ with rfl | rfl
  · constructor
    · omega
    constructor
    · intro _ hn
      rcases (even_iff_exists_two_mul.mp hn) with ⟨m, hm⟩
      subst n
      omega
    constructor
    · intro _ hn
      rcases hn with ⟨m, hm⟩
      subst n
      omega
    · intro h
      omega
  · have hn : Even n := hκ2even rfl
    constructor
    · omega
    constructor
    · intro h
      omega
    constructor
    · intro h
      omega
    · intro h
      rcases (even_iff_exists_two_mul.mp hn) with ⟨m, hm⟩
      subst n
      omega

end MathlibPlus.Algebra
