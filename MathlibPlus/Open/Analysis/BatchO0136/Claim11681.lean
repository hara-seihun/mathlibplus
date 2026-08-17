import Mathlib

namespace MathlibPlus.Open.Analysis.BatchO0136.Claim11681

/-- Claim 11681: normalized linear intertwiners on a free transitive orbit
transport one seed coefficient map uniquely, with both equivalent forms of
the transport equation explicit. -/
def claim11681
    (K W O M : Type*)
    [Field K] [Group W] [MulAction W O]
    [AddCommGroup M] [Module K M]
    (V : O → Type*)
    [∀ o : O, AddCommGroup (V o)]
    [∀ o : O, Module K (V o)]
    (N : ∀ (w : W) (x : O), V x ≃ₗ[K] V (w • x))
    (rho : W →* (M ≃ₗ[K] M)) : Prop :=
  ((∀ x y : O, ∃ g : W, g • x = y) ∧
    (∀ g : W, (∃ x : O, g • x = x) → g = 1) ∧
    (∀ x, HEq (N 1 x) (LinearEquiv.refl K (V x))) ∧
    (∀ (g h : W) (x : O),
      HEq (N (g * h) x) ((N h x).trans (N g (h • x))))) →
    ∀ (x₀ : O) (B₀ : V x₀ →ₗ[K] M),
      ∃! B : ∀ x : O, V x →ₗ[K] M,
        (B x₀ = B₀) ∧
          (∀ (w : W),
            B (w • x₀) =
              (rho w).toLinearMap.comp
                (B₀.comp (N w x₀).symm.toLinearMap)) ∧
          (∀ (g : W) (x : O),
            (B (g • x)).comp (N g x).toLinearMap =
              (rho g).toLinearMap.comp (B x))

end MathlibPlus.Open.Analysis.BatchO0136.Claim11681
