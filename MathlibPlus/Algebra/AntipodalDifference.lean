import MathlibPlus.Basic

namespace MathlibPlus.Algebra.AntipodalDifference

/-- Claim 33433: the normalized antipodal difference on `ZMod 28` changes sign
under the half-period shift. -/
theorem antipodalDifferenceProfile_claim33433
    (s : ZMod 28 → ZMod 3) (hs : s 0 = 0) :
    let δ : ZMod 28 → ZMod 3 := fun b => s (b + 14) - s b
    (∀ b : ZMod 28, δ (b + 14) = -δ b) ∧
      δ 0 = s 14 ∧ δ 14 = -δ 0 := by
  dsimp
  have hperiod : ∀ b : ZMod 28, b + 14 + 14 = b := by
    intro b
    rw [add_assoc]
    rw [show (14 : ZMod 28) + 14 = 0 by decide]
    simp
  constructor
  · intro b
    rw [hperiod b]
    ring
  constructor
  · simp [hs]
  · simpa using (show s (0 + 14 + 14) - s (0 + 14) =
      -(s (0 + 14) - s 0) by
        rw [hperiod 0]
        ring)

end MathlibPlus.Algebra.AntipodalDifference
