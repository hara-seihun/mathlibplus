import Mathlib

namespace MathlibPlus.Algebra

/-- The three identities forced by the defining relations of the central Clifford
family in admitted claim 7903. -/
theorem clifford_family_consequences_claim7903
    {R : Type*} [Ring R] (c X Z : R)
    (hX : X * X = 1) (hZ : Z * Z = c) (hXZ : X * Z = -Z * X) :
    let Y := Z * X
    Y * Y = -c ∧ Z * Y = c * X ∧ Y * Z = -c * X := by
  dsimp
  constructor
  · calc
      (Z * X) * (Z * X) = Z * (X * Z) * X := by noncomm_ring
      _ = Z * (-Z * X) * X := by rw [hXZ]
      _ = -(Z * Z) * (X * X) := by noncomm_ring
      _ = -c := by rw [hZ, hX]; simp
  constructor
  · calc
      Z * (Z * X) = (Z * Z) * X := by noncomm_ring
      _ = c * X := by rw [hZ]
  · calc
      (Z * X) * Z = Z * (X * Z) := by noncomm_ring
      _ = Z * (-Z * X) := by rw [hXZ]
      _ = -(Z * Z) * X := by noncomm_ring
      _ = -c * X := by rw [hZ]

end MathlibPlus.Algebra
