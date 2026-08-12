import MathlibPlus.Basic

namespace MathlibPlus.Analysis.CompressedOperatorIdentity

/-!
Formalization of admitted claim 46444.  The displayed compression identity is
an algebraic identity in a star ring: `P` is a self-adjoint idempotent and `D`
and `Q` are self-adjoint.  The source's operator domains (`ran P`) and its
source-specific assertion about when the leakage terms vanish are not needed
for, and are not silently added to, this identity.
-/

/-- The compressed commutator identity from claim 46444. -/
theorem compressed_commutator_identity_claim46444
    {R : Type*} [Ring R] [StarRing R]
    (P D Q : R)
    (hP : P * P = P) (hPs : star P = P)
    (hDs : star D = D) (hQs : star Q = Q) :
    let A := P * Q * P
    let DP := P * D * P
    let L := (1 - P) * D * P
    let M := (1 - P) * Q * P
    DP * A - A * DP =
      P * (D * Q - Q * D) * P + star M * L - star L * M := by
  dsimp
  simp only [star_mul, star_sub, star_one, hPs, hDs, hQs]
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  have hPP (x : R) : P * (P * x) = P * x := by
    rw [← mul_assoc, hP]
  simp only [← mul_assoc]
  simp only [mul_assoc]
  simp only [hPP]
  noncomm_ring

end MathlibPlus.Analysis.CompressedOperatorIdentity
