import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim18345

/-- The displacement jet `u_j = cᵀ Z^j x`, represented by a dot product. -/
noncomputable def displacementJet {R : Type*} [Semiring R] (N : ℕ)
    (Z : Matrix (Fin N) (Fin N) R) (x c : Fin N → R) : Fin N → R :=
  fun j => dotProduct c (Matrix.mulVec (Z ^ (j : ℕ)) x)

end MathlibPlus.LinearAlgebra.Claim18345
