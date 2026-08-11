import MathlibPlus.Basic

namespace MathlibPlus.Algebra.ProjectiveStokes

/--
The coordinate `Π(z) = -X(z) / D(z)` on the chart where `X(z) D(z)` is
nonzero.  The source statement does not specify the coordinate index type or
field, so both are kept generic; no holomorphic or other ambient hypotheses
are added.
-/
def projectiveStokesCoordinate {ι K : Type*} [Field K]
    (X D : ι → K) (z : {z : ι // X z * D z ≠ 0}) : K :=
  -X z / D z

end MathlibPlus.Algebra.ProjectiveStokes
