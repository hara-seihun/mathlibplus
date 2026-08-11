import Mathlib

namespace MathlibPlus.NumberTheory.GcdIdentities

/-- Claim 10732: the stated positive-integer gcd identity.  The proof reduces
`d` to its residue modulo `12` and checks the twelve possible residues. -/
theorem allDepthGcdIdentity (d : ℕ) (_hdpos : 1 ≤ d) :
    Nat.gcd 4 d * Nat.gcd 6 d = Nat.gcd 2 d * Nat.gcd 12 d := by
  let r := d % 12
  let q := d / 12
  have hr : r < 12 := by
    dsimp [r]
    exact Nat.mod_lt _ (by norm_num)
  have hd : d = r + 12 * q := by
    dsimp [r, q]
    omega
  have h4 : d = r + 4 * (3 * q) := by omega
  have h6 : d = r + 6 * (2 * q) := by omega
  have h2 : d = r + 2 * (6 * q) := by omega
  have hg4 : Nat.gcd 4 d = Nat.gcd 4 r := by
    rw [h4, Nat.gcd_add_mul_left_right]
  have hg6 : Nat.gcd 6 d = Nat.gcd 6 r := by
    rw [h6, Nat.gcd_add_mul_left_right]
  have hg2 : Nat.gcd 2 d = Nat.gcd 2 r := by
    rw [h2, Nat.gcd_add_mul_left_right]
  have hg12 : Nat.gcd 12 d = Nat.gcd 12 r := by
    rw [hd, Nat.gcd_add_mul_left_right]
  rw [hg4, hg6, hg2, hg12]
  interval_cases r <;> norm_num

end MathlibPlus.NumberTheory.GcdIdentities
