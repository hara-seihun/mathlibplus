import Mathlib

namespace MathlibPlus.Open.ProjectsResearch.CI

/-- Claim 60269: the valency-14 and valency-69 CI theorem for C7 × Q12. -/
def coprimeShellProductC7Q12 : Prop :=
  let G := ZMod 7 × QuaternionGroup 3
  ∀ (U V : Set G),
    U ⊆ (Set.univ : Set G) \ {1} →
    V ⊆ (Set.univ : Set G) \ {1} →
    (∀ x, x ∈ U → x⁻¹ ∈ U) →
    (∀ x, x ∈ V → x⁻¹ ∈ V) →
    U.ncard = V.ncard →
    (U.ncard = 14 ∨ U.ncard = 69) →
    SimpleGraph.Iso
        (SimpleGraph.fromRel (fun x y : G => x⁻¹ * y ∈ U))
        (SimpleGraph.fromRel (fun x y : G => x⁻¹ * y ∈ V)) →
      ∃ α : G ≃* G, α '' U = V

end MathlibPlus.Open.ProjectsResearch.CI
