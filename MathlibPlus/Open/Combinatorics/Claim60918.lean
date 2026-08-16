import Mathlib

namespace MathlibPlus.Open

/-- Claim 60918: the specified subspace Cayley graph over `𝔽₂^r × C₉` is CI. -/
def claim60918 : Prop :=
  ∀ (r d : ℕ),
    (r = 3 ∨ r = 4 ∨ r = 5) →
    3 ≤ d →
    d ≤ r →
    ∀ (W : Submodule (ZMod 2) (Fin r → ZMod 2)),
      Module.finrank (ZMod 2) W = d →
      let G := (Fin r → ZMod 2) × ZMod 9
      let S : Set G := {g | g.1 ∈ W ∧ g.2 = 0} \ {0}
      0 ∉ S ∧
        (∀ s ∈ S, -s ∈ S) ∧
        ∀ T : Set G,
          0 ∉ T →
          (∀ t ∈ T, -t ∈ T) →
          (∃ e : G ≃ G,
            ∀ a b : G,
              (a ≠ b ∧ b - a ∈ S) ↔
                (e a ≠ e b ∧ e b - e a ∈ T)) →
          ∃ α : G ≃+ G, Set.image α S = T

end MathlibPlus.Open
