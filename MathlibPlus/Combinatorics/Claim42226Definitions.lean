import Mathlib.Data.Finset.Basic

namespace MathlibPlus.Combinatorics.Claim42226

variable {α : Type*} [DecidableEq α]

/-- The outside support of `A` relative to the fixed set `M`. -/
def outsideSupport (M A : Finset α) : Finset α := A \ M

end MathlibPlus.Combinatorics.Claim42226
