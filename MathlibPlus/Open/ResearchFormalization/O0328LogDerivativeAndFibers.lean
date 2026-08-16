import MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459
import MathlibPlus.Analysis.CompletedGammaFactor

open Filter
open MeasureTheory
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

noncomputable section

/-- The Mellin carrier `M_q(s)` for a real compact source. -/
noncomputable def sourceMellin (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  mellin (fun x : ℝ => (q x : ℂ)) s

/-- The centered coordinate used by the quotient multiplier. -/
def centeredCoordinate (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * z

/-- The centered multiplier `E_q(z)` from the source's `M_q/A` formula. -/
noncomputable def centeredMultiplier (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  let s := centeredCoordinate z
  (1 / 2 : ℂ) *
    (sourceMellin q s /
        MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor s +
      sourceMellin q (1 - s) /
        MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor (1 - s))

/-- The arithmetic-coordinate multiplier `𝓔_q(s)=E_q(-i(s-1/2))`. -/
noncomputable def arithmeticMultiplier (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  centeredMultiplier q (-Complex.I * (s - (1 / 2 : ℂ)))

/-- The arithmetic carrier in Claim 15461. -/
noncomputable def arithmeticCarrier (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * arithmeticMultiplier q s

/-- The de-archimedean logarithmic derivative of the named arithmetic carrier. -/
noncomputable def arithmeticPrimeLogDerivative (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  -deriv (arithmeticCarrier q) s / arithmeticCarrier q s

/-- Claim 15462: logarithmic differentiation of the exact arithmetic carrier. -/
def claim15462 : Prop :=
  ∀ (a R : ℝ),
    0 < a →
      a < R →
        ∀ q : ℝ → ℝ,
          q ∈
              MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass
                a R →
            ∀ s : ℂ,
              arithmeticMultiplier q s ≠ 0 →
                riemannZeta s ≠ 0 →
                  arithmeticPrimeLogDerivative q s =
                    -deriv riemannZeta s / riemannZeta s -
                      deriv (arithmeticMultiplier q) s /
                        arithmeticMultiplier q s

/-- Claim 15466: a continuous linear right inverse corrects convergent jets
without changing the limit of the remaining data. -/
def claim15466 : Prop :=
  ∀ {V B : Type*}
    [TopologicalSpace V] [AddCommGroup V] [Module ℂ V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    [TopologicalSpace B] [AddCommGroup B] [Module ℂ B]
    [IsTopologicalAddGroup B] [ContinuousSMul ℂ B]
    {N : ℕ}
    (T : V →L[ℂ] B)
    (J : V →L[ℂ] (Fin N → ℂ)),
    DenseRange (fun v : V => (T v, J v)) →
    Function.Surjective J →
    ∀ (R : (Fin N → ℂ) →L[ℂ] V),
      (∀ y : Fin N → ℂ, J (R y) = y) →
      ∀ (b : B) (y : Fin N → ℂ) (v : ℕ → V),
        Tendsto (fun n => T (v n)) atTop (𝓝 b) →
        Tendsto (fun n => J (v n)) atTop (𝓝 y) →
        (∀ n : ℕ, J (v n + R (y - J (v n))) = y) ∧
          Tendsto
            (fun n : ℕ => T (v n + R (y - J (v n))))
            atTop (𝓝 b)

end

end MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers
