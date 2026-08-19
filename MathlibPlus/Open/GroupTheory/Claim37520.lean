import Mathlib

namespace MathlibPlus.Open.GroupTheory.Claim37520

/-- Claim 37520: for an identity-fixing bijection of a finite group, the
relative-derivative set criterion is equivalent to preservation of the left
Cayley relation. -/
def claim37520 : Prop :=
  ∀ {H : Type*} [Finite H] [Group H]
    (f : H ≃ H), f 1 = 1 →
    ∀ S : Set H,
      (∀ x y : H,
        ((∃ c ∈ S, y = c * x) ↔
          (∃ t ∈ f '' S, f y = t * f x))) ↔
        (∀ g : H,
          Set.image
              (fun c : H => f.symm (f (c * g) * (f g)⁻¹)) S = S)

end MathlibPlus.Open.GroupTheory.Claim37520
