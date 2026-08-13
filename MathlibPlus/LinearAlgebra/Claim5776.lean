import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim5776

/-- Claim 5776: an exact linear transport identity restricts to the kernels. -/
theorem transport_identity_restricts_to_kernels
    {K U V W Z : Type*} [Semiring K]
    [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid Z]
    [Module K U] [Module K V] [Module K W] [Module K Z]
    (Rmap : U →ₗ[K] V) (Φsource : U →ₗ[K] W)
    (Φtarget : V →ₗ[K] Z) (Q : W →ₗ[K] Z)
    (htransport : Φtarget.comp Rmap = Q.comp Φsource) :
    LinearMap.ker Φsource ≤ (LinearMap.ker Φtarget).comap Rmap ∧
      ∃ r : (LinearMap.ker Φsource) →ₗ[K] (LinearMap.ker Φtarget),
        ∀ x : LinearMap.ker Φsource, (r x : V) = Rmap x := by
  have hmap : LinearMap.ker Φsource ≤ (LinearMap.ker Φtarget).comap Rmap := by
    intro x hx
    rw [Submodule.mem_comap, LinearMap.mem_ker]
    have hzero : Φsource x = 0 := LinearMap.mem_ker.mp hx
    have hcomp : Φtarget (Rmap x) = Q (Φsource x) := by
      have h := LinearMap.congr_fun htransport x
      exact h
    rw [hcomp, hzero, map_zero]
  refine ⟨hmap, ?_⟩
  let r : (LinearMap.ker Φsource) →ₗ[K] (LinearMap.ker Φtarget) :=
    (Rmap.domRestrict (LinearMap.ker Φsource)).codRestrict
      (LinearMap.ker Φtarget) (fun x => hmap x.2)
  refine ⟨r, ?_⟩
  intro x
  rfl

end MathlibPlus.LinearAlgebra.Claim5776
