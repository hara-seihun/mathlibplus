import Mathlib

namespace MathlibPlus.Combinatorics.Claim3972

/-- The unique-fixed-point involutive part of the prescribed card-cocycle
class in claim 3972. -/
def uniqueFixedPointInvolutiveCardCocycle_claim3972
    {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V) : Prop :=
  ∀ i, Function.Involutive (π i) ∧
    {j | π i j = j} = ({i} : Set V)

end MathlibPlus.Combinatorics.Claim3972
