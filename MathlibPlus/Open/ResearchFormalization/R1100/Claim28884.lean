import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationR1100

/-- Claim 28884: under the exact rank-two and nonzero-period hypotheses,
normalization by `F 0` has a full period subgroup that is a proper
one-dimensional subspace. -/
def periodSubgroupIsLine_claim28884
    (F : (Fin 2 → ZMod 3) → (Fin 3 → ZMod 3)) : Prop :=
  Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun x => F x - F 0))) = 2 →
    (∃ s : Fin 2 → ZMod 3, s ≠ 0 ∧ ∀ x, F (x + s) = F x) →
      ∃ K : Submodule (ZMod 3) (Fin 2 → ZMod 3),
        Module.finrank (ZMod 3) K = 1 ∧
          K ≠ ⊤ ∧
          ∀ s, s ∈ K ↔
            ∀ x, (F (x + s) - F 0) = (F x - F 0)

end MathlibPlus.Open.ResearchFormalizationR1100
