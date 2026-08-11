import Mathlib

namespace MathlibPlus.Combinatorics.SymmetricFiveColorCayley

/--
The source's `C₃³` is represented by the additive group `Fin 3 → ZMod 3`.
`Fin 5` is the color set `{0,1,2,3,4}`.  The source writes the identity as
`1`; the additive Lean model writes it as `0`.
-/
def isSymmetricFiveColorCayleyStructure
    (c : (Fin 3 → ZMod 3) → Fin 5) : Prop :=
  c 0 = 0 ∧ ∀ a : Fin 3 → ZMod 3, c (-a) = c a

/-- The surjective five-value slice is the above predicate plus surjectivity. -/
def isSurjectiveSymmetricFiveColorCayleyStructure
    (c : (Fin 3 → ZMod 3) → Fin 5) : Prop :=
  isSymmetricFiveColorCayleyStructure c ∧ Function.Surjective c

end MathlibPlus.Combinatorics.SymmetricFiveColorCayley
