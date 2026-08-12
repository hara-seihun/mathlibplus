import Mathlib

namespace MathlibPlus.Combinatorics

/-- The binary-mask bit vector for a family on an `n`-element ground set has
one bit for each mask `s < 2^n`; `true` means that mask is present. -/
def packedFamilyUnionClosed_claim42317
    (n : ℕ) (bits : Fin (2 ^ n) → Bool) : Prop :=
  ∀ s t : Fin (2 ^ n),
    bits s = true → bits t = true →
      bits ⟨s.val ||| t.val, Nat.or_lt_two_pow s.isLt t.isLt⟩ = true

/-- Bitwise OR of two valid subset masks is again a valid `n`-bit mask. -/
theorem packedFamily_unionMask_valid_claim42317
    {n : ℕ} (s t : Fin (2 ^ n)) :
    s.val ||| t.val < 2 ^ n :=
  Nat.or_lt_two_pow s.isLt t.isLt

end MathlibPlus.Combinatorics
