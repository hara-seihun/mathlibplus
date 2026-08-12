import Mathlib.Algebra.Module.LinearMap.Basic

namespace MathlibPlus.RepresentationTheory.LoweringReturn

/-- Claim 6997.  The source's commutator is the pointwise form of
`L_(k+2) R_k - R_(k-2) L_k = -k`, and its lowest-weight hypothesis is
`L_k F = 0`. -/
theorem loweringReturnIdentity_claim6997
    {V : Type*} [AddCommGroup V]
    (L R : ℤ → V →ₗ[ℤ] V) (k : ℤ) (F : V)
    (hcomm : ∀ v : V,
      L (k + 2) (R k v) - R (k - 2) (L k v) = (-k : ℤ) • v)
    (hlowest : L k F = 0) :
    L (k + 2) (R k F) = (-k : ℤ) • F := by
  have h := hcomm F
  simp [hlowest] at h
  calc
    L (k + 2) (R k F) = -(k • F) := h
    _ = (-k : ℤ) • F := (neg_smul k F).symm

end MathlibPlus.RepresentationTheory.LoweringReturn
