import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra

/--
The algebraic oblique-transport identity from admitted claim 11114.  The
source's `P_v` is represented by the endomorphism parameter `P_v`: no metric,
orthogonality, or unitary hypothesis is used by this identity.
-/
theorem claim11114_obliqueResidualTransport
    {R V W : Type*} [Ring R] [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W]
    (T : V →ₗ[R] W) (L : W →ₗ[R] V)
    (J P_v : V →ₗ[R] V) (v : V)
    (hLT : L.comp T = LinearMap.id) :
    (((LinearMap.id : W →ₗ[R] W) - T.comp (P_v.comp L))
        ((T.comp (J.comp L)) (T v))) =
      T (((LinearMap.id : V →ₗ[R] V) - P_v) (J v)) := by
  have hL (x : V) : L (T x) = x := by
    have h := LinearMap.congr_fun hLT x
    simpa using h
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hL v]
  rw [hL (J v)]
  simp only [LinearMap.id_apply, map_sub]

end MathlibPlus.LinearAlgebra
