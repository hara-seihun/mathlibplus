import Mathlib.GroupTheory.GroupAction.Blocks

namespace MathlibPlus.GroupTheory.Claim28346

/-- Claim 28346: in the regular action of a group on itself, the orbits of a
normal subgroup form a block system.  This records existence of the coset
partition only; it makes no uniqueness claim about invariant block systems. -/
theorem normalSubgroupOrbitsFormBlockSystem
    (G : Type*) [Group G] (N : Subgroup G) [N.Normal] :
    MulAction.IsBlockSystem G (Set.range fun a : G => MulAction.orbit N a) := by
  exact MulAction.IsBlockSystem.of_normal

end MathlibPlus.GroupTheory.Claim28346
