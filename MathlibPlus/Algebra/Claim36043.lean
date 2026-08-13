import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- The physical same-host factorization is the indicated commutative-ring
identity after substituting the two carrier factorizations. -/
theorem claim36043_same_host_factorization
    {R : Type*} [CommRing R]
    (U z P Q M : R) :
    let F_R := U + z * (Q * M)
    let F_S := U + z * (P * M)
    let A := P * F_R
    let B := Q * F_S
    A - B = U * (P - Q) := by
  dsimp
  ring

end MathlibPlus.Algebra
