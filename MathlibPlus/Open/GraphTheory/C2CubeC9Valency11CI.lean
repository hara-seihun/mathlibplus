import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every inverse-closed source connection set of cardinality eleven on
`C₂³ × C₉` has the ordinary Cayley graph-CI property.  The statement uses
`Set.ncard S = 11` for the source valency, as in the admitted claim; it does
not add an identity-exclusion hypothesis absent from the source wording. -/
def c2CubeC9Valency11CI_claim27681 : Prop :=
  let C2 := Multiplicative (ZMod 2)
  let C9 := Multiplicative (ZMod 9)
  let G := C2 × C2 × C2 × C9
  ∀ (S T : Set G),
    (∀ s : G, s ∈ S → s⁻¹ ∈ S) →
    (∀ t : G, t ∈ T → t⁻¹ ∈ T) →
    Set.ncard S = 11 →
    (∃ e : Equiv G G,
      ∀ x y : G,
        (SimpleGraph.mulCayley S).Adj x y ↔
          (SimpleGraph.mulCayley T).Adj (e x) (e y)) →
    ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
