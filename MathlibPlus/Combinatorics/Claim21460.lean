import Mathlib

namespace MathlibPlus.Combinatorics.Claim21460

/-- Exact finite-support carrier for six-coordinate rigidity.  The collection
`validSupports` is the source's valid-support family for one factor. -/
def IsSixCoordinateRigid
    {α : Type*} [DecidableEq α]
    (validSupports : Finset (Finset α)) : Prop :=
  validSupports.card = 1 ∧
    ∀ support ∈ validSupports, support.card = 6

end MathlibPlus.Combinatorics.Claim21460
