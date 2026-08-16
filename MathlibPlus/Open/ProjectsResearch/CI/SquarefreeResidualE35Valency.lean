import Mathlib

namespace MathlibPlus.Open.ProjectsResearch.CI

/-- Claim 60271: low/high valency CI theorem for E(C35,4). -/
def squarefreeResidualE35Valency : Prop :=
  let G := ZMod 35 × ZMod 4
  letI : Mul G :=
    ⟨fun x y =>
      (x.1 + (-1 : ZMod 35) ^ x.2.val * y.1, x.2 + y.2)⟩
  letI : Inv G :=
    ⟨fun x =>
      (-((-1 : ZMod 35) ^ ((-x.2).val) * x.1), -x.2)⟩
  letI : One G := ⟨(0, 0)⟩
  ∀ (U V : Set G),
    U ⊆ (Set.univ : Set G) \ {1} →
    V ⊆ (Set.univ : Set G) \ {1} →
    (∀ x, x ∈ U → x⁻¹ ∈ U) →
    (∀ x, x ∈ V → x⁻¹ ∈ V) →
    U.ncard = V.ncard →
    (U.ncard ≤ 11 ∨ (128 ≤ U.ncard ∧ U.ncard ≤ 139)) →
    SimpleGraph.Iso
        (SimpleGraph.fromRel (fun x y : G => x⁻¹ * y ∈ U))
        (SimpleGraph.fromRel (fun x y : G => x⁻¹ * y ∈ V)) →
      ∃ α : G ≃* G, α '' U = V

end MathlibPlus.Open.ProjectsResearch.CI
