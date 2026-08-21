-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics.Claim20661

/--
The exact thirteen-member union-closed family from claim 20661, represented by
six-bit masks.  The collision shadow is the collection of members containing
coordinate `2`; clearing that bit gives the corresponding lower member.
-/
theorem sharpSixCoordinateUnionClosedExample :
    let H : Finset ℕ := {0, 18, 24, 26, 41, 45, 50, 56, 57, 58, 59, 61, 63}
    let bit : ℕ → ℕ → Prop := fun i m => Nat.testBit m i = true
    let frequency : Finset ℕ → ℕ → ℕ :=
      fun F i => (F.filter (fun m => bit i m)).card
    let deficit : Finset ℕ → ℕ → ℤ :=
      fun F i => (F.card : ℤ) - 2 * (frequency F i : ℤ)
    let collisionShadow : Finset ℕ := H.filter (fun m => bit 2 m)
    H.card = 13 ∧
      (∀ a ∈ H, ∀ b ∈ H, Nat.lor a b ∈ H) ∧
      deficit H 0 = 1 ∧
      deficit H 2 = 7 ∧
      (∀ m ∈ H, bit 2 m → bit 0 m) ∧
      collisionShadow.card = 3 ∧
      (∀ m ∈ collisionShadow,
        m - 2 ^ 2 ∈ H ∧ ¬ bit 2 (m - 2 ^ 2)) ∧
      deficit collisionShadow 1 = 1 ∧
      frequency H 3 > H.card / 2 ∧
      frequency H 4 > H.card / 2 ∧
      frequency H 5 > H.card / 2 := by
  native_decide

end MathlibPlus.Combinatorics.Claim20661
