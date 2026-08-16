import Mathlib

namespace MathlibPlus.Open

namespace Claim60347

variable {G : Type*} [Group G]

/-- The permutation `p_x` from admitted claim 60347. -/
def p (f : Equiv.Perm G) (x : G) : Equiv.Perm G :=
  ((Equiv.mulLeft x).trans f).trans
    ((Equiv.mulLeft (f x)⁻¹).trans f.symm)

/-- The subgroup `P_f` from admitted claim 60347. -/
def P_f (f : Equiv.Perm G) : Subgroup (Equiv.Perm G) :=
  Subgroup.closure (Set.range (p f) ∪ {Equiv.inv G})

end Claim60347

end MathlibPlus.Open
