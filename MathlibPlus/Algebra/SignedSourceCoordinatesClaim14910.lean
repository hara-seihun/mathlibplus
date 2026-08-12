import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 14910: the three signed `N = 1` source matrices give the stated
coordinates for every real symmetric `2 × 2` matrix.  The source matrices are
inlined so that no source-specific auxiliary definition is introduced. -/
theorem signedSourceCoordinates_claim14910 (a b d : ℝ) :
    let Ahalf : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    let Aone : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 2]
    let Aquarter : Matrix (Fin 2) (Fin 2) ℝ :=
      !![(1 : ℝ) / 2, Real.sqrt 2 / Real.pi;
         Real.sqrt 2 / Real.pi, 1 / Real.pi]
    let z : ℝ := Real.pi * b / Real.sqrt 2
    let y : ℝ := (a + d - z * (1 / 2 + 1 / Real.pi)) / 4
    let x : ℝ := (a - d - z * (1 / 2 - 1 / Real.pi)) / 2
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, d]
    M = x • Ahalf + y • Aone + z • Aquarter := by
  dsimp only
  let z : ℝ := Real.pi * b / Real.sqrt 2
  let y : ℝ := (a + d - z * (1 / 2 + 1 / Real.pi)) / 4
  let x : ℝ := (a - d - z * (1 / 2 - 1 / Real.pi)) / 2
  change !![a, b; b, d] =
    x • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) +
      y • (!![2, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ) +
        z • (!![(1 : ℝ) / 2, Real.sqrt 2 / Real.pi;
          Real.sqrt 2 / Real.pi, 1 / Real.pi] : Matrix (Fin 2) (Fin 2) ℝ)
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j
  · change a = x * 1 + y * 2 + z * ((1 : ℝ) / 2)
    field_simp [hpi, hsqrt]
    ring
  · change b = x * 0 + y * 0 + z * (Real.sqrt 2 / Real.pi)
    dsimp [z]
    field_simp [hpi, hsqrt]
    ring
  · change b = x * 0 + y * 0 + z * (Real.sqrt 2 / Real.pi)
    dsimp [z]
    field_simp [hpi, hsqrt]
    ring
  · change d = x * (-1) + y * 2 + z * (1 / Real.pi)
    dsimp [x, y, z]
    field_simp [hpi, hsqrt]
    ring

end MathlibPlus.Algebra
