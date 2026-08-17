import MathlibPlus.Open.GroupTheory.R1349Claim41243

namespace MathlibPlus.Open.GroupTheory.R1349Claim41226

open MathlibPlus.Open.GroupTheory.R1349Claim41243
open MathlibPlus.Open.GroupTheory.CayleyCI

/-- Claim 41226: the pure-`Q₁₂` seven-block pair predicate on the concrete
84-point Cayley carrier. -/
def claim41226
    (S : Set G) (B : Finset (Set G))
    (R T : Subgroup (Equiv.Perm G)) : Prop :=
  pureBlockSystem B ∧
    isRegularRSubgroup (undirectedCayleyAdj S) R ∧
    isRegularRSubgroup (undirectedCayleyAdj S) T ∧
    preservesBlockSystem R B ∧
    preservesBlockSystem T B ∧
    inducedRegularC7 R B ∧
    inducedRegularC7 T B ∧
    let Y := pairGeneratedGroup R T
    let K := blockKernel Y B
    regularQ12OnEveryBlock (R ⊓ K) B ∧
      regularQ12OnEveryBlock (T ⊓ K) B

end MathlibPlus.Open.GroupTheory.R1349Claim41226
