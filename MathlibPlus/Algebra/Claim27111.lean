import Mathlib

namespace MathlibPlus.Algebra.Claim27111

/-- The displayed finite-difference functional and its parameter recurrence from claim 27111.
The local function `P` is the value sequence of the source polynomial, and `Δ` is
forward difference on that sequence. -/
theorem finiteDifferenceSummation
    (M r s : ℕ) (P : ℕ → ℚ) :
    let N := M - 2 * r
    let Δ : (ℕ → ℚ) → (ℕ → ℚ) := fun f n => f (n + 1) - f n
    let Λ : ℕ → ℕ → ℕ → (ℕ → ℚ) → ℚ := fun N s r f =>
      (-1 : ℚ) ^ s *
        (∑ j ∈ Finset.range (N - s + 1),
          (Nat.choose (N - s) j : ℚ) * ((Δ^[s]) f) (r + j))
    Λ N s r P =
        (-1 : ℚ) ^ s *
          (∑ j ∈ Finset.range (N - s + 1),
            (Nat.choose (N - s) j : ℚ) * ((Δ^[s]) P) (r + j)) ∧
      (1 ≤ s → Λ N s r P = -Λ (N - 1) (s - 1) r (Δ P)) := by
  dsimp
  constructor
  · rfl
  · intro hs
    cases s with
    | zero => omega
    | succ s =>
      simp
      have hsub : (M - 2 * r - 1) - s = M - 2 * r - (Nat.succ s) := by
        omega
      rw [hsub]
      ring

end MathlibPlus.Algebra.Claim27111
