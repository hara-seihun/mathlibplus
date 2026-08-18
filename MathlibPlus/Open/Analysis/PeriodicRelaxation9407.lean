import MathlibPlus.Open.Analysis.CommensuratePolynomial
import MathlibPlus.Open.FormalizationBatch.Claims9408And9428

namespace MathlibPlus.Open.Analysis

noncomputable section

def commensuratePeriod_9407 (q : ℤ) : ℝ :=
  2 * Real.pi / Real.log (q : ℝ)

def criticalLineCoordinate_9407 (t : ℝ) : ℂ :=
  (1 : ℂ) - 1 / ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)

def criticalBase_9407 (q : ℤ) (t : ℝ) : ℂ :=
  let qR : ℝ := (q : ℝ)
  let L : ℝ := Real.log qR
  let r : ℝ := Real.rpow qR (-1 / 2 : ℝ)
  let z : ℂ := criticalLineCoordinate_9407 t
  let Z : ℂ := z * riemannZeta (1 / (1 - z))
  let Phi : ℂ → ℂ := fun w =>
    Complex.exp (-((L : ℂ) / 2) * ((1 + w) / (1 - w)))
  Z * (1 - (r : ℂ) * Phi z) / ((1 : ℂ) - (r : ℂ) ^ 2)

def commensuratePeriodicMultiplier_9407
    (q : ℤ) (Q : Polynomial ℂ) (t : ℝ) : ℂ :=
  let qR : ℝ := (q : ℝ)
  let L : ℝ := Real.log qR
  let r : ℝ := Real.rpow qR (-1 / 2 : ℝ)
  Polynomial.eval
    (Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I))) Q /
    Polynomial.eval (r : ℂ) Q

def reflectedCommensurateChoice_9407
    (q : ℤ) (Q : Polynomial ℂ) (t : ℝ) : ℂ :=
  criticalBase_9407 q t * commensuratePeriodicMultiplier_9407 q Q t

def periodicRelaxation_9407 : Prop :=
  ∀ (q : ℤ), (2 : ℤ) ≤ q →
    ∀ Q : Polynomial ℂ,
      (∀ z : ℂ, ‖z‖ < 1 → Polynomial.eval z Q ≠ 0) →
        (∀ t : ℝ,
          commensuratePeriodicMultiplier_9407 q Q
              (t + commensuratePeriod_9407 q) =
            commensuratePeriodicMultiplier_9407 q Q t) ∧
          ∃ g : ℝ → ℂ,
            Measurable g ∧
              (∀ t : ℝ, g (t + commensuratePeriod_9407 q) = g t) ∧
                (∀ t : ℝ,
                  g t = commensuratePeriodicMultiplier_9407 q Q t) ∧
                  (∀ t : ℝ,
                    reflectedCommensurateChoice_9407 q Q t =
                      criticalBase_9407 q t * g t)

end

end MathlibPlus.Open.Analysis
