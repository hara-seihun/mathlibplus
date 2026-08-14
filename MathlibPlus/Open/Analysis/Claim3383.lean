import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def primitiveCompletedTheta (u : ℝ) : ℝ :=
  ∑' q : {q : ℕ // 0 < q},
    Real.exp (-Real.pi * (q.1 : ℝ) ^ 2 * Real.exp (2 * u))

noncomputable def primitiveCompletedThetaMoment (n : ℕ) : ℝ :=
  (2 : ℝ) / (Nat.factorial (2 * n) : ℝ) *
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (u / 2) * primitiveCompletedTheta u * u ^ (2 * n)

noncomputable def adjacentDeterminant (m n : ℕ) : ℝ :=
  if m = 0 then 1 else
    Matrix.det (fun i j : Fin m =>
      primitiveCompletedThetaMoment (n - i.1 + j.1))

noncomputable def principalLambertW (z : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ x * Real.exp x = z}

noncomputable def lambertArgument (n : ℕ) : ℝ :=
  principalLambertW (2 * (n : ℝ) / Real.pi)

noncomputable def determinantGamma (n : ℕ) : ℝ :=
  lambertArgument n / (1 + lambertArgument n)

def adjacentDeterminantReserve : Prop :=
  (∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 0 < N ∧
      ∃ error : ℕ → ℕ → ℝ,
        (∀ n : ℕ, N ≤ n → ∀ m : ℕ,
          1 ≤ m → (m : ℝ) ≤ A * Real.sqrt (n : ℝ) →
            |error n m| ≤ C *
              (1 / (lambertArgument n) ^ 2 + (m : ℝ) / (n : ℝ))) ∧
        (∀ n : ℕ, N ≤ n → ∀ m : ℕ,
          1 ≤ m → (m : ℝ) ≤ A * Real.sqrt (n : ℝ) →
            adjacentDeterminant (m + 1) n * adjacentDeterminant (m - 1) n /
                adjacentDeterminant m n ^ 2 =
              (2 * determinantGamma n * (m : ℝ) / (n : ℝ)) *
                (1 + error n m))) ∧
  (∀ x : ℝ, 0 < x →
    ∃ error : ℕ → ℝ,
      Filter.Tendsto error Filter.atTop (nhds 0) ∧ ∃ N : ℕ, 0 < N ∧
        (∀ n : ℕ, N ≤ n →
          1 ≤ Nat.floor (x * Real.sqrt (n : ℝ)) ∧
          adjacentDeterminant (Nat.floor (x * Real.sqrt (n : ℝ)) + 1) n *
              adjacentDeterminant (Nat.floor (x * Real.sqrt (n : ℝ)) - 1) n /
              adjacentDeterminant (Nat.floor (x * Real.sqrt (n : ℝ))) n ^ 2 =
            (2 * determinantGamma n * x / Real.sqrt (n : ℝ)) *
              (1 + error n)))

end MathlibPlus.Open.Analysis
