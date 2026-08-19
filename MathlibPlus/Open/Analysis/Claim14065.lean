import MathlibPlus.Open.Analysis.Claims14059_14062_14064_14067
import MathlibPlus.Open.Analysis.GammaZetaMellinApplication

open MeasureTheory
open Set
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim14065

noncomputable section

/-- Claim 14065: for the exact logarithmic-tilt law, symmetrization has the
squared characteristic function and the analytic logarithmic curvature obeys
the two-point Bochner bound. -/
def symmetrizedTwoPointBochnerInequality_claim14065 : Prop :=
  let q : ℝ → ℝ := fun x => 1 / x - 1 / (Real.exp x - 1)
  let F : ℂ → ℂ := fun s =>
    ∫ x in Ioi (0 : ℝ),
      Complex.cpow (x : ℂ) (s - (1 : ℂ)) * (q x : ℂ)
  let μ : ℝ → Measure ℝ := fun σ =>
    volume.withDensity
      (fun y =>
        ENNReal.ofReal
          (Real.exp (σ * y) * q (Real.exp y) / (F (σ : ℂ)).re))
  let φ : ℝ → ℝ → ℂ := fun σ t =>
    F ((σ : ℂ) + (t : ℂ) * Complex.I) / F (σ : ℂ)
  let reflected : ℝ → Measure ℝ := fun σ =>
    Measure.map (fun y : ℝ => -y) (μ σ)
  let symmetrized : ℝ → Measure ℝ := fun σ =>
    Measure.conv (μ σ) (reflected σ)
  let convolutionPower : Measure ℝ → ℕ → Measure ℝ :=
    fun ν n =>
      Nat.rec (Measure.dirac (0 : ℝ))
        (fun _ acc => Measure.conv acc ν) n
  let infinitelyDivisible : Measure ℝ → Prop := fun ν =>
    IsProbabilityMeasure ν ∧
      ∀ n : ℕ, 0 < n →
        ∃ root : Measure ℝ,
          IsProbabilityMeasure root ∧
            convolutionPower root n = ν
  let localLogOfF : ℝ → (ℂ → ℂ) → Prop := fun σ K =>
    ∀ t : ℝ,
      F ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 →
        ∃ r : ℝ, 0 < r ∧
          ∀ s : ℂ,
            ‖s - ((σ : ℂ) + (t : ℂ) * Complex.I)‖ < r →
              Complex.exp (K s) = F s ∧ AnalyticAt ℂ K s
  ∀ (σ : ℝ) (K : ℂ → ℂ),
    0 < σ →
      σ < 1 →
        localLogOfF σ K →
          (∀ t : ℝ,
            Complex.exp
                (K ((σ : ℂ) + (t : ℂ) * Complex.I) - K (σ : ℂ)) =
              φ σ t) →
            infinitelyDivisible (symmetrized σ) →
              (∀ t : ℝ,
                (∫ y : ℝ,
                    Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))
                      ∂(symmetrized σ)) =
                  (Complex.normSq (φ σ t) : ℂ)) ∧
                (let H : ℝ → ℂ := fun t =>
                  ((2 * (deriv (deriv K)
                    ((σ : ℂ) + (t : ℂ) * Complex.I)).re : ℝ) : ℂ)
                 let positiveDefinite : Prop :=
                   ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
                     let S : ℂ := ∑ i, ∑ j,
                       star (c i) * c j * H (x i - x j)
                     S.im = 0 ∧ 0 ≤ S.re
                 positiveDefinite ∧
                   (deriv (deriv K) (σ : ℂ)).im = 0 ∧
                     ∀ t : ℝ,
                       |(deriv (deriv K)
                           ((σ : ℂ) + (t : ℂ) * Complex.I)).re| ≤
                         (deriv (deriv K) (σ : ℂ)).re)

end

end MathlibPlus.Open.Analysis.Claim14065
