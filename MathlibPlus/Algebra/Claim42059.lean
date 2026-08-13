import Mathlib

namespace MathlibPlus.Algebra.Claim42059

/-- In an odd cyclic group, the only element fixed by inversion is zero. -/
theorem neg_eq_self_iff_zero_of_odd {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (a : ZMod n) :
    -a = a ↔ a = 0 := by
  rcases hn with ⟨k, rfl⟩
  haveI : NeZero (2 * k + 1) := ⟨by omega⟩
  constructor
  · intro h
    rw [ZMod.neg_eq_self_iff] at h
    rcases h with h | h
    · exact h
    · exfalso
      omega
  · intro h
    simp [h]

end MathlibPlus.Algebra.Claim42059
