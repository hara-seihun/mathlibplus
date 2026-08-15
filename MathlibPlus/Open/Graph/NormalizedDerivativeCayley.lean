import Mathlib

namespace MathlibPlus.Open

/-- Claim 28566: the normalized-derivative orbit criterion for a Cayley
relation. -/
def normalizedDerivativeCayleyAutomorphismCriterion : Prop :=
  ∀ (G : Type*) [Group G] (S : Set G) (f : G ≃ G),
    f 1 = 1 →
      let normalizedDerivative :=
        fun (g : G) =>
          ((Equiv.mulRight g).trans f).trans
            (Equiv.mulRight ((f g)⁻¹))
      let Df : Subgroup (Equiv.Perm G) :=
        Subgroup.closure
          (Set.range (fun g : G =>
            (normalizedDerivative g).trans f.symm))
      (∀ x y : G,
        (y * x⁻¹ ∈ S ↔ f y * (f x)⁻¹ ∈ S)) ↔
        (Set.image f S = S ∧
          ∀ d : Df,
            Set.image (d : Equiv.Perm G) S = S)

end MathlibPlus.Open
