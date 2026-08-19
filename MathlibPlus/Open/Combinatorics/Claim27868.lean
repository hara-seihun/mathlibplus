import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim27868

abbrev TernaryPlane := ZMod 3 × ZMod 3

/-- Claim 27868: normalizing the value at the origin leaves exactly eight
free ternary values, hence `3^(9-1) = 3^8 = 6561` functions. -/
def claim27868 : Prop :=
  Fintype.card {φ : TernaryPlane → ZMod 3 // φ (0, 0) = 0} = 3 ^ (9 - 1) ∧
    3 ^ (9 - 1) = 3 ^ 8 ∧
    3 ^ 8 = 6561

end MathlibPlus.Open.Combinatorics.Claim27868
