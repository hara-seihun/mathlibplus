import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim11100

/-- The reciprocal diagonal action preserves the split form `J`; the displayed
sum-of-squares decomposition, with its invertible change of coordinates, is the
exact `(1,1)` inertia certificate. -/
theorem reciprocalDynamics_splitForm
    (x : Fin 2 → ℝ) :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, (1 / 2 : ℝ)]
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let split : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
      fun y => ![y 0 + y 1, y 0 - y 1]
    U.transpose * J * U = J ∧
      Function.Bijective split ∧
      (∑ i, ∑ j, x i * J i j * x j) =
        (1 / 2 : ℝ) * (x 0 + x 1) ^ 2 -
          (1 / 2 : ℝ) * (x 0 - x 1) ^ 2 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · constructor
    · intro y z h
      have h0 : y 0 + y 1 = z 0 + z 1 := by
        simpa using congrFun h 0
      have h1 : y 0 - y 1 = z 0 - z 1 := by
        simpa using congrFun h 1
      funext i
      fin_cases i
      · change y 0 = z 0
        linarith
      · change y 1 = z 1
        linarith
    · intro y
      refine ⟨![((y 0 + y 1) / 2), ((y 0 - y 1) / 2)], ?_⟩
      funext i
      fin_cases i <;> simp <;> ring
  · simp [Fin.sum_univ_two]
    ring

end MathlibPlus.LinearAlgebra.Claim11100
