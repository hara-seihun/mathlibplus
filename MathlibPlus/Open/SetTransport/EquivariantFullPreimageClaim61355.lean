import Mathlib

namespace MathlibPlus.Open.SetTransport

/-- The admitted equivariant full-preimage transport statement and its
surjective reflection of set equality. -/
def equivariantFullPreimageClaim61355 : Prop :=
  ∀ {X Y : Type*} (q : X → Y) (e : X ≃ X) (f : Y ≃ Y),
    q ∘ e = f ∘ q →
      (∀ S : Set Y,
        e '' (q ⁻¹' S) = q ⁻¹' (f '' S)) ∧
      (Function.Surjective q →
        ∀ S T : Set Y,
          f '' S = T ↔
            e '' (q ⁻¹' S) = q ⁻¹' T)

end MathlibPlus.Open.SetTransport
