import Mathlib

open Matrix
open scoped ComplexOrder

namespace MathlibPlus.LinearAlgebra

/-- Constant channel aggregation is matrix congruence compression.  In the
finite matrix interface, a positive-semidefinite Fourier kernel remains
positive semidefinite after the compression by a fixed channel matrix. -/
theorem constantAggregation_posSemidef_claim15152
    {X m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜]
    (K : X → Matrix m m 𝕜) (P : Matrix m n 𝕜)
    (hK : ∀ x, (K x).PosSemidef) :
    ∀ x, (Pᴴ * K x * P).PosSemidef := by
  classical
  intro x
  exact (hK x).conjTranspose_mul_mul_same P

end MathlibPlus.LinearAlgebra
