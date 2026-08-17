import MathlibPlus.Open.Analysis.AllOrderCheckerboardWickRotation

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.K0034Claim7796

open MathlibPlus.Open.Analysis

noncomputable section

/-- The complex-valued centered generator used for the uncentered ray jets. -/
noncomputable def complexRankinGenerator (α : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) * deriv f u + ((α - u : ℝ) : ℂ) / 2 * f u

/-- The centered jet values in the reviewed finite-matrix carrier. -/
noncomputable def complexRankinQ (α : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  centeredRankinQValue α n u

/-- The original ray jets with an unrestricted complex scalar mean. -/
noncomputable def complexRankinP (α : ℝ) (μ : ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => 1
  | n + 1 => fun u =>
      complexRankinGenerator α (complexRankinP α μ n) u +
        μ * complexRankinP α μ n u

noncomputable def complexRankinInner (α : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ),
    star (f u) * g u * (centeredRankinRadialWeight α u : ℂ)

noncomputable def uncenteredRankinHankel (α : ℝ) (μ : ℂ) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j =>
    complexRankinInner α (fun _ : ℝ => 1)
      (complexRankinP α μ ((i : ℕ) + (j : ℕ)))

noncomputable def uncenteredRankinGram (α : ℝ) (μ : ℂ) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j =>
    complexRankinInner α (complexRankinP α μ (i : ℕ))
      (complexRankinP α μ (j : ℕ))

/-- Exact centered and uncentered one-sided determinant laws. -/
def claim7796 : Prop :=
  ∀ (α : ℝ) (m : ℕ),
    0 < α →
      (∀ i j : Fin (m + 1),
        balancedRankinGram α m i j =
          ((-1 : ℂ) ^ (i : ℕ)) * oneSidedRankinHankel α m i j) ∧
      Matrix.det (oneSidedRankinHankel α m) =
        ((-1 : ℂ) ^ (m * (m + 1) / 2)) *
          Matrix.det (balancedRankinGram α m) ∧
      (∀ (μ : ℂ),
        (∀ (j : ℕ) (u : ℝ),
          complexRankinP α μ j u =
            ∑ r ∈ Finset.range (j + 1),
              (Nat.choose j r : ℂ) * μ ^ (j - r) * complexRankinQ α r u) ∧
        Matrix.det (uncenteredRankinHankel α μ m) =
            Matrix.det (oneSidedRankinHankel α m) ∧
          Matrix.det (uncenteredRankinGram α μ m) =
            Matrix.det (balancedRankinGram α m) ∧
          Matrix.det (uncenteredRankinHankel α μ m) =
            ((-1 : ℂ) ^ (m * (m + 1) / 2)) *
              Matrix.det (uncenteredRankinGram α μ m))

end

end MathlibPlus.Open.ResearchFormalization.K0034Claim7796
