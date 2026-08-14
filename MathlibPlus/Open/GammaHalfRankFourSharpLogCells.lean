import Mathlib

namespace MathlibPlus.Open

noncomputable def gammaHalfRankFourSharpLogCells : Prop :=
  let gammaDensity : ℝ → ℝ :=
    fun z =>
      Real.exp (-z) * Real.rpow z ((1 : ℝ) / 2 - 1) /
        Real.Gamma ((1 : ℝ) / 2)
  let P : ℕ → ℝ → ℝ :=
    fun j y =>
      ∫ z in Set.Ioi (0 : ℝ),
        (y + z) ^ (2 * j) * gammaDensity z
  let strictlyChebyshevOn : ℕ → ℝ → ℝ → Prop :=
    fun k a b =>
      ∀ r : ℕ, 1 ≤ r → r ≤ k + 1 →
        ∀ y : Fin r → ℝ,
          (∀ i : Fin r, a < y i ∧ y i < b) →
          StrictMono y →
          0 < Matrix.det (fun (i : Fin r) (j : Fin r) => P (j : ℕ) (y i))
  let specialPoints : Fin 5 → ℝ :=
    fun i => ((70 + i.1 : ℕ) : ℝ) / 100
  (∀ n : ℕ, 2 ≤ n →
      ∀ r : ℕ,
        (r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) →
          ∀ y : Fin r → ℝ,
            (∀ i : Fin r,
              Real.log (n : ℝ) < y i ∧
                y i < Real.log ((n + 1 : ℕ) : ℝ)) →
            StrictMono y →
            0 < Matrix.det
              (fun (i : Fin r) (j : Fin r) => P (j : ℕ) (y i))) ∧
    (∀ i : Fin 5,
      Real.log (2 : ℝ) < specialPoints i ∧
        specialPoints i < Real.log (3 : ℝ)) ∧
    Matrix.det
        (fun (i : Fin 5) (j : Fin 5) => P (j : ℕ) (specialPoints i)) =
      -((24473996510523397768899 : ℝ) /
        (195312500000000000000000000000000000 : ℝ)) ∧
    (∀ n : ℕ, 2 ≤ n →
      strictlyChebyshevOn 3 (Real.log (n : ℝ))
        (Real.log ((n + 1 : ℕ) : ℝ))) ∧
    ¬ strictlyChebyshevOn 4 (Real.log (2 : ℝ)) (Real.log (3 : ℝ))

end MathlibPlus.Open
