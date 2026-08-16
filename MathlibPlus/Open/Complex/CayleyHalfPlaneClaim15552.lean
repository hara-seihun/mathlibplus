import Mathlib

namespace MathlibPlus.Complex.CayleyHalfPlane

noncomputable section

/-- Claim 15552: the Cayley map `(z - 1) / (z + 1)` is a biholomorphism
from the open right half-plane onto the open unit disk. -/
def cayley_biholomorphic_claim15552 : Prop :=
  let cayleyMap : ℂ → ℂ := fun z => (z - 1) / (z + 1)
  let cayleyInverse : ℂ → ℂ := fun w => (1 + w) / (1 - w)
  let rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}
  let openUnitDisk : Set ℂ := {w : ℂ | ‖w‖ < 1}
  IsOpen rightHalfPlane ∧
    IsOpen openUnitDisk ∧
    Set.MapsTo cayleyMap rightHalfPlane openUnitDisk ∧
    Set.MapsTo cayleyInverse openUnitDisk rightHalfPlane ∧
    (∀ z ∈ rightHalfPlane, cayleyInverse (cayleyMap z) = z) ∧
    (∀ w ∈ openUnitDisk, cayleyMap (cayleyInverse w) = w) ∧
    (∀ z ∈ rightHalfPlane, DifferentiableAt ℂ cayleyMap z) ∧
    (∀ w ∈ openUnitDisk, DifferentiableAt ℂ cayleyInverse w)

end

end MathlibPlus.Complex.CayleyHalfPlane
