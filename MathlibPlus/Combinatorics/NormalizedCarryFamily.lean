import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Combinatorics.NormalizedCarryFamily

/-! Formalization of admitted claim 39672. -/

/-- There are exactly `3^8` functions `𝔽₃² → 𝔽₃` that vanish at the origin. -/
theorem normalized_functions_card :
    Fintype.card {q : (ZMod 3 × ZMod 3) → ZMod 3 // q (0, 0) = 0} = 3 ^ 8 := by
  native_decide

end MathlibPlus.Combinatorics.NormalizedCarryFamily
