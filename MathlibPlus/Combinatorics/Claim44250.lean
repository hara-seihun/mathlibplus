import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim44250

/-- The exact complementary-pair transition and its zero-residual criterion.

The local `pair` sequence starts at `(n, 1)` and iterates the displayed greedy
transition.  On a positive pair, the first coordinate of the next pair is zero
exactly at the equality state `R = S`; the positivity hypotheses are explicit
because the recurrence itself subsequently permits a zero coordinate.
-/
theorem complementaryPairRecurrence :
    let step : ℕ × ℕ → ℕ × ℕ := fun p =>
      if p.1 ≥ p.2 then (p.1 - p.2, 2 * p.2 + 1)
      else (2 * p.1, p.2 - p.1 + 1)
    let pair : ℕ → ℕ → ℕ × ℕ :=
      fun n k => Nat.rec (n, 1) (fun _ p => step p) k
    (∀ (R S : ℕ),
        step (R, S) =
          if R ≥ S then (R - S, 2 * S + 1) else (2 * R, S - R + 1)) ∧
      (∀ (n k : ℕ), pair n (k + 1) = step (pair n k)) ∧
      (∀ (n k : ℕ),
        0 < (pair n k).1 → 0 < (pair n k).2 →
          ((pair n (k + 1)).1 = 0 ↔ (pair n k).1 = (pair n k).2)) := by
  simp only
  constructor
  · intro R S
    trivial
  constructor
  · intro n k
    trivial
  · intro n k hR hS
    let p : ℕ × ℕ := Nat.rec (n, 1) (fun _ p =>
      if p.1 ≥ p.2 then (p.1 - p.2, 2 * p.2 + 1)
      else (2 * p.1, p.2 - p.1 + 1)) k
    change ((if p.1 ≥ p.2 then (p.1 - p.2, 2 * p.2 + 1)
      else (2 * p.1, p.2 - p.1 + 1)).1 = 0 ↔ p.1 = p.2)
    change 0 < p.1 at hR
    change 0 < p.2 at hS
    by_cases h : p.1 ≥ p.2
    · simp only [if_pos h]
      omega
    · simp only [if_neg h]
      omega

end MathlibPlus.Combinatorics.Claim44250
