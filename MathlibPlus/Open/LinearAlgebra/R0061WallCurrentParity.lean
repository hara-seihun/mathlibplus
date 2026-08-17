import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.R0061WallCurrentParity

noncomputable section

private def shearA (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, a; 0, 1]

private def shearB (b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; b, 1]

private def commutator (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  shearA a * shearB b * shearA (-a) * shearB (-b)

/-- Claim 17591: simultaneous sign reversal leaves the diagonal entries of
 the exact two-shear commutator even and changes the signs of its off-diagonal
 entries. -/
def parityOfWallCurrentTransmission_claim17591 : Prop :=
  ∀ (a b : ℝ),
    commutator (-a) (-b) 0 0 = commutator a b 0 0 ∧
    commutator (-a) (-b) 1 1 = commutator a b 1 1 ∧
    commutator (-a) (-b) 0 1 = -commutator a b 0 1 ∧
    commutator (-a) (-b) 1 0 = -commutator a b 1 0

end
end MathlibPlus.Open.LinearAlgebra.R0061WallCurrentParity
