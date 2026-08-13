import Mathlib

namespace MathlibPlus.Algebra.Claim10382

/--
The algebraic Cartan contraction used by the nonzero-resonance claim.  Once
`L` is invertible, the Cartan identity and commutation of `L` with `d` imply
that `ι L⁻¹` is a contracting homotopy.  The resonant-complex and nilpotent
Jordan-block packaging belongs to the source application; the hypotheses
here expose exactly the operator calculation used by it.
-/
theorem cartanContractingHomotopy_claim10382
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (d ι L Linv : Module.End R M)
    (hCartan : d.comp ι + ι.comp d = L)
    (hComm : d.comp L = L.comp d)
    (hLeft : Linv.comp L = 1)
    (hRight : L.comp Linv = 1) :
    d.comp (ι.comp Linv) + (ι.comp Linv).comp d = 1 := by
  have hInvComm : Linv.comp d = d.comp Linv := by
    calc
      Linv.comp d = (Linv.comp d).comp (L.comp Linv) := by
        rw [hRight, LinearMap.comp_id]
      _ = Linv.comp (d.comp L).comp Linv := by
        simp [LinearMap.comp_assoc]
      _ = Linv.comp (L.comp d).comp Linv := by
        rw [hComm]
      _ = (Linv.comp L).comp d.comp Linv := by
        simp [LinearMap.comp_assoc]
      _ = d.comp Linv := by
        rw [hLeft, LinearMap.id_comp]
  calc
    d.comp (ι.comp Linv) + (ι.comp Linv).comp d =
        (d.comp ι).comp Linv + ι.comp (Linv.comp d) := by
          simp [LinearMap.comp_assoc]
    _ = (d.comp ι).comp Linv + ι.comp (d.comp Linv) := by
          rw [hInvComm]
    _ = (d.comp ι + ι.comp d).comp Linv := by
          simp [LinearMap.add_comp, LinearMap.comp_assoc]
    _ = L.comp Linv := by
          rw [hCartan]
    _ = 1 := hRight

end MathlibPlus.Algebra.Claim10382
