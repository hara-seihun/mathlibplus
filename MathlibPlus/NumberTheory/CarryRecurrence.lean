import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory.Claim35659

/-- Appending a binary digit to a carry has exactly the two child carries
listed in admitted claim 35659.  The source does not specify the scalar
ambient type; the carry calculation is stated over the integers. -/
theorem appendDigitCarry (r q k d : ℤ) (hd : d = 0 ∨ d = 1) :
    let rNext : ℤ := 2 * r - q * (k + 1) * d
    rNext = 2 * r ∨ rNext = 2 * r - q * (k + 1) := by
  dsimp
  rcases hd with rfl | rfl <;> simp

end MathlibPlus.NumberTheory.Claim35659
