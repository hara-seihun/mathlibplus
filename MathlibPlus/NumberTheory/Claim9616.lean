import Mathlib

namespace MathlibPlus.NumberTheory

/-- The all-depth collision of the two strand-roster formulas from claim 9616. -/
theorem allDepthRosterCollision_claim9616 (depth : ℕ) :
    Nat.gcd 4 depth * Nat.gcd 6 depth =
      Nat.gcd 2 depth * Nat.gcd 12 depth := by
  have gcdFour :
      Nat.gcd 4 depth = Nat.gcd 4 (depth % 12) := by
    calc
      Nat.gcd 4 depth
          = Nat.gcd 4
              (depth % 12 + (3 * (depth / 12)) * 4) := by
            congr 2
            omega
      _ = Nat.gcd 4 (depth % 12) :=
        Nat.gcd_add_mul_right_right 4 _ _
  have gcdSix :
      Nat.gcd 6 depth = Nat.gcd 6 (depth % 12) := by
    calc
      Nat.gcd 6 depth
          = Nat.gcd 6
              (depth % 12 + (2 * (depth / 12)) * 6) := by
            congr 2
            omega
      _ = Nat.gcd 6 (depth % 12) :=
        Nat.gcd_add_mul_right_right 6 _ _
  have gcdTwo :
      Nat.gcd 2 depth = Nat.gcd 2 (depth % 12) := by
    calc
      Nat.gcd 2 depth
          = Nat.gcd 2
              (depth % 12 + (6 * (depth / 12)) * 2) := by
            congr 2
            omega
      _ = Nat.gcd 2 (depth % 12) :=
        Nat.gcd_add_mul_right_right 2 _ _
  have gcdTwelve :
      Nat.gcd 12 depth = Nat.gcd 12 (depth % 12) := by
    calc
      Nat.gcd 12 depth
          = Nat.gcd 12
              (depth % 12 + (depth / 12) * 12) := by
            congr 2
            omega
      _ = Nat.gcd 12 (depth % 12) :=
        Nat.gcd_add_mul_right_right 12 _ _
  rw [gcdFour, gcdSix, gcdTwo, gcdTwelve]
  have remainder_lt : depth % 12 < 12 :=
    Nat.mod_lt depth (by norm_num)
  interval_cases depth % 12 <;>
    norm_num

end MathlibPlus.NumberTheory
