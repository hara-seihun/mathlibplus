import Mathlib

namespace MathlibPlus.Combinatorics.RoutineClaimFormalizations

/-- The unique-fixed-point involutive card-cocycle class described in claim
3972. -/
def uniqueFixedPointInvolutiveCardCocycle_claim3972
    {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V) : Prop :=
  ∀ i : V, Function.Involutive (π i) ∧
    {x : V | π i x = x} = ({i} : Set V)

end MathlibPlus.Combinatorics.RoutineClaimFormalizations
