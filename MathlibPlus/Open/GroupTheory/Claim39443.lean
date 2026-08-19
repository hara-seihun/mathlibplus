import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- A finite p-prime affine action on a finite-dimensional `ZMod p`-space has
an affine fixed point. -/
def finitePrimeAffineFixedPoint_claim39443 : Prop :=
  ∀ (p : ℕ), ∀ hp : p.Prime,
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (G V : Type*) [Fintype G] [Group G]
      [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V],
      ¬ p ∣ Fintype.card G →
      ∀ φ : G →* (V ≃ᵃ[ZMod p] V),
        ∃ v : V, ∀ g : G, φ g v = v

end MathlibPlus.Open.GroupTheory
