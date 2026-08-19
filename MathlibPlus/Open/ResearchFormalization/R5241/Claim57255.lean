import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5241.Claim57255

noncomputable section

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

def wInvSOne : Matrix2 :=
  !![1, 0; 1, -1]

def fOne (a : ℝ) : Matrix2 :=
  !![1, 2 * a + 1; 0, 2]

def betaOne (a : ℝ) : Matrix2 :=
  wInvSOne * fOne a

/-- The exact dimension-one cup-transform matrix and its boundary. -/
def claim57255 : Prop :=
  wInvSOne = !![1, 0; 1, -1] ∧
    (∀ a : ℝ, fOne a = !![1, 2 * a + 1; 0, 2]) ∧
    (∀ a : ℝ,
      betaOne a = !![1, 2 * a + 1; 1, 2 * a - 1] ∧
        betaOne a 1 1 = 2 * a - 1) ∧
    (∀ a : ℝ, 0 ≤ a → a < (1 / 2 : ℝ) → betaOne a 1 1 < 0) ∧
    betaOne (1 / 2 : ℝ) 1 1 = 0

end
end MathlibPlus.Open.ResearchFormalization.R5241.Claim57255
