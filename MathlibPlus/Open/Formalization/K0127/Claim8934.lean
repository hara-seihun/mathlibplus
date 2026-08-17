import MathlibPlus.Open.Analysis.ExplicitLogarithmicPotentialDifference
import MathlibPlus.Open.Formalization.K0127

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Topology

namespace MathlibPlus.Open.Formalization.K0127.Claim8934

noncomputable section

private def equilibriumMeasure : Measure ℝ :=
  Measure.withDensity (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun z => ENNReal.ofReal
      (MathlibPlus.Open.Analysis.equilibriumDensity
        MathlibPlus.Open.Analysis.potentialEndpoint z))

private def gaussianZeroData (p : ℕ → Polynomial ℝ)
    (y : ℕ → ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    (∀ x : ℝ,
      Polynomial.eval x (p n) =
        MathlibPlus.Open.Formalization.K0127.gaussianZeroPolynomial y n x) ∧
      (∀ j ∈ Finset.Icc 1 n, 0 < y n j) ∧
      (∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
        j < k → y n k < y n j)

private def record18StieltjesTransforms (y : ℕ → ℕ → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s →
    Tendsto
      (fun n : ℕ =>
        ∫ z : ℝ, (s + z ^ 2)⁻¹ ∂
          (MathlibPlus.Open.Formalization.K0127.gaussianNodeMeasure y n))
      atTop
      (𝓝 (∫ z : ℝ, (s + z ^ 2)⁻¹ ∂equilibriumMeasure))

private def finiteVagueSubsequentialLimit
    (ν : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧
    ∃ q : ℕ → ℕ, StrictMono q ∧
      ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
        Tendsto
          (fun k : ℕ => ∫ z : ℝ, f z ∂(ν (q k)))
          atTop
          (𝓝 (∫ z : ℝ, f z ∂μ))

private def noMassEscapesToInfinity (y : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ R : ℝ, 0 < R ∧
      ∀ᶠ n : ℕ in atTop,
        MathlibPlus.Open.Formalization.K0127.gaussianNodeMeasure y n
            (Set.Ioi R) < ENNReal.ofReal ε

private def weaklyConverges
    (ν : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f →
    Bornology.IsBounded (Set.range f) →
      Tendsto
        (fun n : ℕ => ∫ z : ℝ, f z ∂(ν n))
        atTop
        (𝓝 (∫ z : ℝ, f z ∂μ))

/-- Record-18 transforms identify every finite vague limit and force the
normalized Gaussian-node measures to converge weakly to the unit equilibrium. -/
def claim8934 : Prop :=
  ∀ (p : ℕ → Polynomial ℝ) (y : ℕ → ℕ → ℝ),
    gaussianZeroData p y →
      record18StieltjesTransforms y →
        equilibriumMeasure Set.univ = 1 ∧
          (∀ μ : Measure ℝ,
            finiteVagueSubsequentialLimit
              (fun n : ℕ =>
                MathlibPlus.Open.Formalization.K0127.gaussianNodeMeasure y n)
              μ →
              μ = equilibriumMeasure) ∧
          noMassEscapesToInfinity y ∧
          weaklyConverges
            (fun n : ℕ =>
              MathlibPlus.Open.Formalization.K0127.gaussianNodeMeasure y n)
            equilibriumMeasure

end

end MathlibPlus.Open.Formalization.K0127.Claim8934
