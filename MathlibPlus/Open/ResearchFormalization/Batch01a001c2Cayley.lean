import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Cayley

/-- The odd-map construction of two inverse-closed Cayley connection sets and
its triangular coordinate isomorphism. -/
def claim53080 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 ≤ p → p % 2 = 1 →
    ∀ (X Z : Type*) [AddCommGroup X] [Module (ZMod p) X]
      [AddCommGroup Z] [Module (ZMod p) Z]
      [FiniteDimensional (ZMod p) X] [FiniteDimensional (ZMod p) Z]
      (g : X → Z),
      g 0 = 0 → (∀ x, g (-x) = -g x) →
      let H : X → Submodule (ZMod p) Z :=
        fun u => Submodule.span (ZMod p)
          (Set.range (fun x : X => g (x + u) - g x - g u))
      let S₀ : Set (X × Z) :=
        {q | ∃ u : X, u ≠ 0 ∧ q.1 = u ∧ q.2 ∈ H u}
      let Sg : Set (X × Z) :=
        {q | ∃ u : X, u ≠ 0 ∧ q.1 = u ∧
          ∃ z : Z, z ∈ H u ∧ q.2 = z + g u}
      let Θ : X × Z → X × Z := fun q => (q.1, q.2 + g q.1)
      (∀ u : X, H (-u) = H u) ∧
      (∀ q, q ∈ S₀ → q ≠ (0, 0)) ∧
      (∀ q, q ∈ Sg → q ≠ (0, 0)) ∧
      (∀ q, q ∈ S₀ → -q ∈ S₀) ∧
      (∀ q, q ∈ Sg → -q ∈ Sg) ∧
      Function.Bijective Θ ∧
      (∀ q₁ q₂ : X × Z,
        q₂ - q₁ ∈ S₀ ↔ Θ q₂ - Θ q₁ ∈ Sg)

end MathlibPlus.Open.ResearchFormalization.Cayley
