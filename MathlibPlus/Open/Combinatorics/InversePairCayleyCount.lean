import MathlibPlus.Basic

namespace MathlibPlus.Open.Combinatorics

/-!
Claim 27980 uses the additive model `C₇² = ZMod 7 × ZMod 7`.  An undirected
Cayley connection set is a finite subset of the nonzero group elements that is
closed under additive inversion.  The finite count is retained as one registry
node rather than replacing it by an unproved computational assertion.
-/
def inversePairCayleyConnectionSetCount : Prop :=
  let G := ZMod 7 × ZMod 7
  Fintype.card {x : G // x ≠ 0} = 48 ∧
    Fintype.card {S : Finset G //
      0 ∉ S ∧ ∀ x : G, x ∈ S → -x ∈ S} = 2 ^ 24

end MathlibPlus.Open.Combinatorics
