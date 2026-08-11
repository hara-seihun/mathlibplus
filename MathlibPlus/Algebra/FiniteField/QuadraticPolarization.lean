import Mathlib

namespace MathlibPlus.Algebra.FiniteField

/-- The quadratic map used in the `𝔽₃²` affine-table model is recovered exactly from
its two coordinate polarizations. -/
theorem quadraticPolarizationF3 (i j : ZMod 3) :
    let Q : (ZMod 3 × ZMod 3) → (Fin 3 → ZMod 3) := fun x ↦
      ![x.1 * (x.1 - 1), (2 * x.1 - 1) * x.2, x.2 ^ 2]
    let B := fun s x ↦ Q (x + s) - Q x - Q s
    Q (i, j) =
      (2 * (i - 1)) • B (1, 0) (i, j) +
        (2 * j) • B (0, 1) (i, j) := by
  dsimp
  have h4 : (4 : ZMod 3) = 1 := by decide
  have h8 : (8 : ZMod 3) = 2 := by decide
  funext k
  fin_cases k <;> simp <;> ring_nf <;> simp [h4, h8]

end MathlibPlus.Algebra.FiniteField
