import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The rank-at-most-five coloured-core obstruction from claim 59239.

A pointed permutation of an odd-prime vector space that simultaneously carries
any finite family of directed Cayley colours to target colours is forced to
have one common linear transporter when the vector-space rank is at most five.
-/
def rankAtMostFiveColouredCoreObstruction : Prop :=
  ∀ (p : ℕ), ∀ hp : p.Prime, 2 < p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (W : Type*) [AddCommGroup W] [Module (ZMod p) W]
      [FiniteDimensional (ZMod p) W],
      Module.finrank (ZMod p) W ≤ 5 →
      ∀ (m : ℕ) (B D : Fin m → Set W),
        ∀ q : W ≃ W, q 0 = 0 →
          (∀ (i : Fin m) (x y : W),
            y - x ∈ B i ↔ q y - q x ∈ D i) →
          ∃ A : W ≃ₗ[ZMod p] W, ∀ i, A '' B i = D i

end MathlibPlus.Open.GraphTheory

