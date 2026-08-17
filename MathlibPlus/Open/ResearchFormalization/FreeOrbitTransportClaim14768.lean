import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.FreeOrbitTransportClaim14768

noncomputable section

/-- The carrier `O` is the orbit itself; freeness is not imposed on an
ambient type containing further orbits. -/
def freeOrbitTransport_claim14768 : Prop :=
  ∀ (𝕜 W O M : Type*) [Field 𝕜] [Group W] [Finite W]
    [MulAction W O] [AddCommGroup M] [Module 𝕜 M]
    (lambda0 : O) (V : O → Type*)
    [∀ lam : O, AddCommGroup (V lam)]
    [∀ lam : O, Module 𝕜 (V lam)]
    (N : ∀ (g : W) (lam : O), V lam ≃ₗ[𝕜] V (g • lam))
    (ρ : W →* (M ≃ₗ[𝕜] M))
    (B₀ : V lambda0 →ₗ[𝕜] M),
    (∀ (g : W) (lam : O), g • lam = lam → g = 1) →
      (∀ lam : O,
        HEq (N 1 lam) (LinearEquiv.refl 𝕜 (V lam))) →
      (∀ (g h : W) (lam : O),
        HEq (N (g * h) lam)
          ((N h lam).trans (N g (h • lam)))) →
      (∀ lam : O, ∃ w : W, w • lambda0 = lam) →
      ∃! B : ∀ lam : O, V lam →ₗ[𝕜] M,
        B lambda0 = B₀ ∧
          (∀ (g : W) (lam : O),
            (B (g • lam)).comp (N g lam).toLinearMap =
              (ρ g).toLinearMap.comp (B lam)) ∧
          (∀ w : W,
            B (w • lambda0) =
              (ρ w).toLinearMap.comp
                (B₀.comp (N w lambda0).symm.toLinearMap))

end
end MathlibPlus.Open.ResearchFormalization.FreeOrbitTransportClaim14768
