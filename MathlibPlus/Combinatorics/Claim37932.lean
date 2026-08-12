import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim37932

abbrev F₃ := ZMod 3

/-- The normalized carry functions in claim 37932. -/
def NormalizedCarry :=
  {q : F₃ → F₃ → F₃ // q 0 0 = 0}

deriving instance Fintype for NormalizedCarry

/-- The square-top carry map from claim 37932. -/
def squareTopCarry (q : F₃ → F₃ → F₃)
    (x u v w : F₃) : F₃ × F₃ × F₃ × F₃ :=
  (x + v ^ 2, u + q v w, v, w)

/-- There are exactly `3^8` normalized carry functions. -/
theorem normalizedCarry_card :
    Fintype.card NormalizedCarry = 3 ^ 8 := by
  native_decide

/-- The displayed decimal count is `6561`. -/
theorem normalizedCarry_card_eq_6561 :
    Fintype.card NormalizedCarry = 6561 := by
  rw [normalizedCarry_card]
  norm_num

end MathlibPlus.Combinatorics.Claim37932
