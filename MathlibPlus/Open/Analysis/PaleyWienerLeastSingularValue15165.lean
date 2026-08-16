import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatchO0267ColumnErrors

open Filter
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.PaleyWienerLeastSingularValue15165

noncomputable section

/-- The exterior Shannon-coordinate index set after anchoring the samples
`0,...,M-1`. -/
def ExteriorIndex (M : ℕ) :=
  {n : ℤ // MathlibPlus.Open.Analysis.FormalizationBatchO0267.exteriorInteger M n}

/-- Infinite square-summable data on the two exterior Shannon tails. -/
abbrev ExteriorL2 (M : ℕ) := lp (fun _ : ExteriorIndex M => ℂ) 2

/-- The Euclidean evaluation-data carrier. -/
abbrev EvaluationSpace (N : ℕ) := EuclideanSpace ℂ (Fin N)

/-- One normalized exterior-Cauchy entry of the anchored evaluation map. -/
noncomputable def anchoredEntry
    (M : ℕ) (z : ℂ) (n : ExteriorIndex M) : ℂ :=
  MathlibPlus.Open.Analysis.FormalizationBatch.normalizedRowFactor z /
    (Complex.ofReal Real.pi * (z - (n.1 : ℂ)))

/-- The anchored evaluation operator from the infinite exterior `ℓ²` domain
into the Euclidean space of normalized evaluation coordinates. -/
noncomputable def anchoredEvaluationOperator
    (M N : ℕ) (nodes : Fin N → ℂ) :
    ExteriorL2 M → EvaluationSpace N :=
  fun a =>
    (EuclideanSpace.equiv (Fin N) ℂ).symm
      (fun j =>
        ∑' n : ExteriorIndex M,
          anchoredEntry M (nodes j) n * a n)

/-- The coordinate of `T_M^* v` at an exterior Shannon index. -/
noncomputable def adjointCoordinate
    (M N : ℕ) (nodes : Fin N → ℂ)
    (v : EvaluationSpace N) (n : ExteriorIndex M) : ℂ :=
  ∑ j : Fin N,
    starRingEnd ℂ (anchoredEntry M (nodes j) n) * v j

/-- The codomain Rayleigh carrier for `T_M T_M^*`. -/
noncomputable def gramRayleigh
    (M N : ℕ) (nodes : Fin N → ℂ) (v : EvaluationSpace N) : ℝ :=
  ∑' n : ExteriorIndex M, ‖adjointCoordinate M N nodes v n‖ ^ 2

/-- The smallest Gram Rayleigh value on unit Euclidean codomain vectors. -/
noncomputable def gramMinimum
    (M N : ℕ) (nodes : Fin N → ℂ) : ℝ :=
  sInf {q : ℝ | ∃ v : EvaluationSpace N,
    ‖v‖ = 1 ∧ q = gramRayleigh M N nodes v}

/-- The nonzero, codomain-side least singular-value carrier. -/
noncomputable def leastSingularValue
    (M N : ℕ) (nodes : Fin N → ℂ) : ℝ :=
  Real.sqrt (gramMinimum M N nodes)

/-- The central rectangle hypothesis for normalized complex evaluations. -/
def centralRectangle
    (M : ℕ) (rho : ℝ) (nodes : Fin N → ℂ) : Prop :=
  ∀ j : Fin N,
    ‖nodes j - Complex.ofReal
        (MathlibPlus.Open.Analysis.FormalizationBatchO0267.anchorCenter M)‖ ≤
      rho * (M : ℝ)

/-- The uniform `O(M)` height hypothesis. -/
def heightBound
    (M : ℕ) (C₀ : ℝ) (nodes : Fin N → ℂ) : Prop :=
  ∀ j : Fin N, |(nodes j).im| ≤ C₀ * (M : ℝ)

/-- Claim 15165: under the central-rectangle and `O(M)` height hypotheses,
the normalized anchored evaluation map has the stated exponentially small
codomain-side least singular value and equivalent Gram minimum. -/
def claim15165 : Prop :=
  ∀ (rho C₀ : ℝ),
    0 ≤ rho → rho < (1 : ℝ) / 2 → 0 < C₀ →
      ∃ q C₁ : ℝ,
        0 < q ∧ q < 1 ∧ 0 < C₁ ∧
          ∀ᶠ M : ℕ in atTop,
            ∀ (N : ℕ), 1 ≤ N →
              ∀ nodes : Fin N → ℂ,
                centralRectangle M rho nodes →
                  heightBound M C₀ nodes →
                    let r : ℕ := (N - 1) / 2
                    leastSingularValue M N nodes ≤
                        C₁ * Real.sqrt (N : ℝ) * q ^ r ∧
                      leastSingularValue M N nodes ^ 2 =
                        gramMinimum M N nodes ∧
                      gramMinimum M N nodes ≤
                        C₁ ^ 2 * (N : ℝ) * q ^ (2 * r)

end

end MathlibPlus.Open.Analysis.PaleyWienerLeastSingularValue15165
