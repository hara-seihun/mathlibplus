import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 16565: the direct product C₇ × S₃ is an undirected CI-group. -/
def c7TimesS3UndirectedCI_claim16565 : Prop :=
  let G := Multiplicative (ZMod 7) × Equiv.Perm (Fin 3)
  ∀ (S T : Set G),
    S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
        ∃ φ : G ≃* G, φ '' S = T

end MathlibPlus.Open.GraphTheory
