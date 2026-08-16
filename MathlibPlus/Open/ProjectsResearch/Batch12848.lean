import Mathlib

namespace MathlibPlus.Open

/--
Conjugation by the fixed reflection on symmetric two-by-two matrices has the
claimed even/odd block decomposition.  The coordinates of
`H = [[A, B], [B, C]]` are recorded by a three-coordinate vector, so the
reflection has signs `(1, -1, 1)`.
-/
def reflection_equivariant_sym2_block_decomposition : Prop :=
  let R : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  let H : (Fin 3 → ℂ) → Matrix (Fin 2) (Fin 2) ℂ :=
    fun v => !![v 0, v 1; v 1, v 2]
  let ρ : (Fin 3 → ℂ) → (Fin 3 → ℂ) :=
    fun v => ![v 0, -v 1, v 2]
  (∀ v, H (ρ v) = R * H v * R) ∧
    ∀ T : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ),
      (∀ v, T (ρ v) = ρ (T v)) →
        ∃ a b c d lambdaCoeff : ℂ, ∀ v,
          H (T v) =
            !![a * v 0 + b * v 2, lambdaCoeff * v 1;
               lambdaCoeff * v 1, c * v 0 + d * v 2]

end MathlibPlus.Open
