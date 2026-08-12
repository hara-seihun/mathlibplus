import Mathlib

namespace MathlibPlus.Algebra.Claim16416

/-- The generalized-Bell polynomial sequence from the displayed recurrence.
The zero index is a harmless sentinel because the source starts at one. -/
noncomputable def generalizedBell : ℕ → Polynomial ℚ
  | 0 => 0
  | n + 1 =>
      Nat.rec (Polynomial.X - Polynomial.C (3 / 2 : ℚ))
        (fun _ p =>
          (Polynomial.X - Polynomial.C (5 / 4 : ℚ)) * p -
            Polynomial.X * p.derivative) n

end MathlibPlus.Algebra.Claim16416
