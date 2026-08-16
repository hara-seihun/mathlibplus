import Mathlib

namespace MathlibPlus.Open

/-- In `F_7`, the specified elements are distinct nontrivial cube roots of unity,
with the stated quotient. -/
def claim60778 : Prop :=
  let lambdaV : ZMod 7 := 2
  let lambdaE : ZMod 7 := 4
  lambdaV ^ 3 = 1 ∧
    lambdaE ^ 3 = 1 ∧
    lambdaV ≠ 1 ∧
    lambdaE ≠ 1 ∧
    lambdaE * lambdaV⁻¹ = 2 ∧
    (2 : ZMod 7) ≠ 1

end MathlibPlus.Open
