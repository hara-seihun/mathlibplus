import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim5777

/-!
Formalization of admitted claim 5777.  The source's ambient transport identity
is retained as `Φ_target ∘ R = Q ∘ Φ_source`; the restricted map is constructed
from the ambient `R` and proved to land in the target kernel.  Finite kernel
dimension is represented by `Module.finrank`.
-/

/-- An injective transport whose ambient square commutes induces an injective
map from the source kernel to the target kernel, so target deficiency is at
least source deficiency. -/
theorem kernelFinrank_le_of_injectiveTransport_claim5777
    {𝕜 V W V' W' : Type*}
    [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W]
    [AddCommGroup V'] [Module 𝕜 V']
    [AddCommGroup W'] [Module 𝕜 W']
    [Module.Finite 𝕜 V] [Module.Finite 𝕜 V']
    (Φ_source : V →ₗ[𝕜] W) (Φ_target : V' →ₗ[𝕜] W')
    (R : V →ₗ[𝕜] V') (Q : W →ₗ[𝕜] W')
    (htransport : Φ_target.comp R = Q.comp Φ_source)
    (hR : Function.Injective
      ((R.domRestrict (LinearMap.ker Φ_source)).codRestrict
        (LinearMap.ker Φ_target) (by
          intro x
          rw [LinearMap.mem_ker]
          have hx := congrArg (fun f => f (x : V)) htransport
          change Φ_target (R (x : V)) = 0
          calc
            Φ_target (R (x : V)) = Q (Φ_source (x : V)) := by
              simpa [LinearMap.comp_apply] using hx
            _ = 0 := by rw [x.property]; simp))) :
    Module.finrank 𝕜 (LinearMap.ker Φ_source) ≤
      Module.finrank 𝕜 (LinearMap.ker Φ_target) := by
  exact LinearMap.finrank_le_finrank_of_injective hR

end MathlibPlus.LinearAlgebra.Claim5777
