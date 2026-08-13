import Mathlib

namespace MathlibPlus.Combinatorics.Claim21354

/-- The number of shifted pendant bits in an ordered branch-five target. -/
def shiftedPendantBitCount (ε : Fin 7 → Bool) : ℕ :=
  (Finset.univ.filter (fun i => ε i = true)).card

/-- The target grade from claim 21354. -/
def targetGrade (X Y Z W : ℕ) (ε : Fin 7 → Bool) : ℕ :=
  X + Y + Z + W + 7 + shiftedPendantBitCount ε

/-- On positive internal lengths, the target grade is the sum of the four
internal lengths, seven base units, and the seven-bit Hamming weight. -/
theorem targetGrade_formula (X Y Z W : ℕ) (ε : Fin 7 → Bool)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (hW : 0 < W) :
    targetGrade X Y Z W ε =
      X + Y + Z + W + 7 +
        (Finset.univ.filter (fun i => ε i = true)).card := by
  rfl

end MathlibPlus.Combinatorics.Claim21354
