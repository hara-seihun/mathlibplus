import MathlibPlus.Open.ResearchFormalization.Batch

noncomputable section

open Set Filter

namespace MathlibPlus.Open.ResearchFormalization.Claim15548

/-- The radial maximum of an entire function on the closed disk of radius `R`. -/
noncomputable def radialMaximum (M : ℂ → ℂ) (R : ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖M z‖) '' {z : ℂ | ‖z‖ ≤ R})

/-- The finite zero-order normalization used at the origin. -/
def originNormalization (M F : ℂ → ℂ) (m : ℕ) : Prop :=
  Differentiable ℂ F ∧
    F 0 ≠ 0 ∧
      ∀ z : ℂ, M z = z ^ m * F z

/-- The exact subexponential meaning of `log M_max(R) = exp(o(R))`. -/
def subexponentialRadialLogGrowth (M : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ R : ℝ in Filter.atTop,
      Real.log (radialMaximum M R) ≤ Real.exp (ε * R)

/-- The prime-counting asymptotic appearing in the Jensen threshold. -/
def primeLogCountingAsymptotic : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    (fun R : ℝ =>
      (MathlibPlus.Open.ResearchFormalization.Batch.primeCountingAt (Real.exp R) : ℝ))
    (fun R : ℝ => Real.exp R / R)

/--
The prime-log zero set forces exponential radial growth.  The first conclusion
records the usual finite-order normalization at the origin; the displayed
Jensen lower bound is on the original radial maximum, and the second
conclusion is the corresponding exclusion of subexponential entire
multipliers without a finite-order hypothesis.
-/
def claim15548 : Prop :=
  primeLogCountingAsymptotic ∧
    ∀ M : ℂ → ℂ,
      Differentiable ℂ M →
        (∃ z : ℂ, M z ≠ 0) →
          (∀ p : ℕ, Nat.Prime p →
            M (MathlibPlus.Open.ResearchFormalization.Batch.primeLogPoint p) = 0) →
            ((∃ m : ℕ, ∃ F : ℂ → ℂ,
                originNormalization M F m ∧
                  (∀ p : ℕ, Nat.Prime p →
                    F (MathlibPlus.Open.ResearchFormalization.Batch.primeLogPoint p) = 0) ∧
                  (∃ c : ℝ, 0 < c ∧
                    ∀ B : ℝ, ∃ R : ℝ,
                      B ≤ R ∧ 0 < R ∧
                        c *
                            (MathlibPlus.Open.ResearchFormalization.Batch.primeCountingAt
                              (Real.exp R) : ℝ) ≤
                          Real.log (radialMaximum M (2 * R)))) ∧
              (subexponentialRadialLogGrowth M →
                ∀ z : ℂ, M z = 0))

end MathlibPlus.Open.ResearchFormalization.Claim15548
