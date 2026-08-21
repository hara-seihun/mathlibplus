-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics.Claim51597

/-- The two displayed rows have a strictly finer lexicographic order than either
row individually; their two-element family is not closed under addition. -/
theorem nonadditiveEscapeFixture :
    let r₁ : Fin 3 → ℤ := ![0, 0, 1]
    let r₂ : Fin 3 → ℤ := ![0, 1, 0]
    let A : Set (Fin 3 → ℤ) := {r₁, r₂}
    let lex : (ℤ × ℤ) → (ℤ × ℤ) → Prop :=
      fun u v => u.1 < v.1 ∨ (u.1 = v.1 ∧ u.2 < v.2)
    ( (∀ i j : Fin 3, i.val < j.val →
          lex (r₁ i, r₂ i) (r₁ j, r₂ j)) ∧
      ¬ (∀ i j : Fin 3, i.val < j.val → r₁ i < r₁ j) ∧
      ¬ (∀ i j : Fin 3, i.val < j.val → r₂ i < r₂ j) ∧
      (r₁ + r₂) ∉ A ) := by
  native_decide

end MathlibPlus.Combinatorics.Claim51597
