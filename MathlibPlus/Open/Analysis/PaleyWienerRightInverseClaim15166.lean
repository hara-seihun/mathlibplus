import MathlibPlus.Open.Analysis.FormalizationBatchO0267

open Filter
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.PaleyWienerRightInverseClaim15166

noncomputable section

/-- The remaining exterior Shannon-coordinate index set. -/
def exteriorIndex (M : ℕ) :=
  {n : ℤ // n < 0 ∨ (M : ℤ) ≤ n}

abbrev ExteriorL2 (M : ℕ) :=
  lp (fun _ : exteriorIndex M => ℂ) 2

/-- The Euclidean `ℓ²` evaluation-data carrier. -/
abbrev EvaluationData (N : ℕ) :=
  EuclideanSpace ℂ (Fin N)

/-- The fixed harmless Shannon-column sign. -/
def exteriorColumnSign (n : ℤ) : ℂ :=
  (-1 : ℂ) ^ n.natAbs

/-- The normalized exterior Cauchy entry, including the removable value at
an exterior integer evaluation node. -/
noncomputable def normalizedExteriorEntry (z : ℂ) (n : ℤ) : ℂ :=
  if z = (n : ℂ) then 1 else
    exteriorColumnSign n *
      (MathlibPlus.Open.Analysis.FormalizationBatch.normalizedRowFactor z /
        (Complex.ofReal Real.pi * (z - (n : ℂ))))

/-- The exact anchored exterior Cauchy formula, presented in the Euclidean
`ℓ²` evaluation-data carrier. -/
noncomputable def anchoredEvaluationFormula
    (M N : ℕ) (nodes : Fin N → ℂ) : ExteriorL2 M → EvaluationData N :=
  fun a =>
    (EuclideanSpace.equiv (Fin N) ℂ).symm
      (fun j : Fin N =>
        ∑' n : exteriorIndex M,
          normalizedExteriorEntry (nodes j) n.1 * a n)

/-- A bounded anchored operator is required to agree with the exact exterior
Cauchy formula, not an unconstrained operator callback. -/
def isAnchoredEvaluationOperator
    (M N : ℕ) (nodes : Fin N → ℂ)
    (T : ExteriorL2 M →L[ℂ] EvaluationData N) : Prop :=
  ∀ a : ExteriorL2 M,
    T a = anchoredEvaluationFormula M N nodes a

/-- Onto-ness of the exact bounded anchored evaluation operator. -/
def anchoredEvaluationOnto
    (T : ExteriorL2 M →L[ℂ] EvaluationData N) : Prop :=
  Function.Surjective T

/-- A bounded right inverse of the exact anchored evaluation operator. -/
def isAnchoredEvaluationRightInverse
    (T : ExteriorL2 M →L[ℂ] EvaluationData N)
    (R : EvaluationData N →L[ℂ] ExteriorL2 M) : Prop :=
  ∀ y : EvaluationData N, T (R y) = y

/-- The central rectangle condition for the normalized evaluation nodes. -/
def centralRectangle
    (M : ℕ) (rho : ℝ) (nodes : Fin N → ℂ) : Prop :=
  ∀ j : Fin N,
    ‖nodes j -
        Complex.ofReal (((M : ℝ) - 1) / 2)‖ ≤
      rho * (M : ℝ)

/-- The uniform `O(M)` imaginary-height condition. -/
def linearHeightBound
    (M : ℕ) (C₀ : ℝ) (nodes : Fin N → ℂ) : Prop :=
  ∀ j : Fin N,
    |(nodes j).im| ≤ C₀ * (M : ℝ)

/-- The scale in the right-inverse lower bound. -/
noncomputable def rightInverseLowerBoundScale
    (C₁ q : ℝ) (N : ℕ) : ℝ :=
  C₁⁻¹ * Real.rpow (N : ℝ) (-((1 : ℝ) / 2)) *
    Real.rpow q (-(((N - 1) / 2 : ℕ) : ℝ))

/-- Claim 15166.  In the fixed central rectangle and linear-height regime,
onto-ness of the exact bounded anchored operator forces the displayed
right-inverse cost, and positive-density data then have exponential cost. -/
def rightInverseLowerBoundAndPositiveDensity15166 : Prop :=
  ∀ (rho C₀ : ℝ),
    0 < rho →
    rho < 1 / 2 →
    0 < C₀ →
      ∃ C₁ q : ℝ,
        0 < C₁ ∧
        0 < q ∧
        q < 1 ∧
          (∀ᶠ M : ℕ in atTop,
            (∀ (N : ℕ),
              1 ≤ N →
                ∀ (nodes : Fin N → ℂ),
                  centralRectangle M rho nodes →
                    linearHeightBound M C₀ nodes →
                      ∀ T : ExteriorL2 M →L[ℂ] EvaluationData N,
                        isAnchoredEvaluationOperator M N nodes T →
                          anchoredEvaluationOnto T →
                            ∀ R : EvaluationData N →L[ℂ] ExteriorL2 M,
                              isAnchoredEvaluationRightInverse T R →
                                ‖R‖ ≥
                                  rightInverseLowerBoundScale C₁ q N) ∧
            (∀ kappa : ℝ,
              0 < kappa →
                ∃ c : ℝ,
                  0 < c ∧
                    ∀ᶠ M : ℕ in atTop,
                      ∀ (N : ℕ),
                        1 ≤ N →
                          kappa * (M : ℝ) ≤ (N : ℝ) →
                            ∀ (nodes : Fin N → ℂ),
                              centralRectangle M rho nodes →
                                linearHeightBound M C₀ nodes →
                                  ∀ T : ExteriorL2 M →L[ℂ]
                                      EvaluationData N,
                                    isAnchoredEvaluationOperator
                                      M N nodes T →
                                      anchoredEvaluationOnto T →
                                        ∀ R :
                                            EvaluationData N →L[ℂ]
                                              ExteriorL2 M,
                                          isAnchoredEvaluationRightInverse T R →
                                            Real.exp (c * (M : ℝ)) ≤ ‖R‖))

end

end MathlibPlus.Open.Analysis.PaleyWienerRightInverseClaim15166
