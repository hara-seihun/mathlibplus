import Mathlib

open scoped BigOperators Topology
open MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.O0336

noncomputable section

private noncomputable def cauchyTransform
    (ν : ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  ν.integral
    (fun t : ℝ => (z + (t : ℂ))⁻¹)
    (ContinuousLinearMap.mul ℝ ℂ)

private def simplePoleWithResidue
    (F : ℂ → ℂ) (p c : ℂ) : Prop :=
  MeromorphicAt F p ∧
    meromorphicOrderAt F p = (-1 : ℤ) ∧
      meromorphicTrailingCoeffAt F p = c

private def finiteAtomicEdge
    (ν : ComplexMeasure ℝ) (r' : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (n : ℕ) (t : Fin n → ℝ),
    (∀ j : Fin n, t j ∈ Icc 0 r') ∧
      (∀ j : Fin n, ν {t j} ≠ 0) ∧
        ν.restrict (Icc 0 r') =
          ∑ j : Fin n, (ν {t j}) • VectorMeasure.dirac (t j) (1 : ℂ) ∧
          (∀ j : Fin n,
            simplePoleWithResidue F (-(t j : ℂ)) (ν {t j})) ∧
            (∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) r' →
              (meromorphicOrderAt F z < (0 : ℤ) ↔
                ∃ j : Fin n, z = -(t j : ℂ)))

/-- Claim 15508: a meromorphic continuation of a finite Cauchy transform
atomizes the measure on each smaller reflected edge, with the atom masses as
its simple-pole residues. -/
def claim15508_localCauchyTransformAtomization : Prop :=
  ∀ (R r : ℝ) (ν : ComplexMeasure ℝ),
    0 < R →
      0 < r →
        IsFiniteMeasure ν.variation →
          ν.variation.support ⊆ Icc 0 R →
            (∃ F : ℂ → ℂ,
              MeromorphicOn F (Metric.ball (0 : ℂ) r) ∧
                (∀ z : ℂ,
                  z ∈ Metric.ball (0 : ℂ) r →
                    0 < z.re → F z = cauchyTransform ν z) ∧
                (∀ r' : ℝ,
                  0 < r' →
                    r' < r →
                      r' < R →
                        ¬ meromorphicOrderAt F (-(r' : ℂ)) < (0 : ℤ) →
                          finiteAtomicEdge ν r' F))

private def finiteCompactSignedMeasure
    (μ : SignedMeasure ℝ) : Prop :=
  IsFiniteMeasure μ.variation ∧
    ∃ K : Set ℝ, IsCompact K ∧ μ.variation Kᶜ = 0

private def zetaLogBranch (logZeta : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ logZeta {w : ℂ | 1 < w.re} ∧
    (∀ w : ℂ, 1 < w.re →
      Complex.exp (logZeta w) = riemannZeta w) ∧
      (∀ x : ℝ, 1 < x → (logZeta (x : ℂ)).im = 0)

private noncomputable def signedComplexIntegral
    (μ : SignedMeasure ℝ) (f : ℝ → ℂ) : ℂ :=
  (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
    (∫ x, f x ∂μ.toJordanDecomposition.negPart)

private noncomputable def shiftedZetaExponential
    (μ : SignedMeasure ℝ) (logZeta : ℂ → ℂ) : ℂ → ℂ :=
  fun s =>
    Complex.exp
      (signedComplexIntegral μ (fun α : ℝ => logZeta (s + (α : ℂ))))

private noncomputable def translatedLowerEdge
    (μ : SignedMeasure ℝ) (a ε : ℝ) : SignedMeasure ℝ :=
  (μ.restrict (Icc a (a + ε))).map (fun α : ℝ => α - a)

/-- Claim 15510: after translating the finite signed measure at its lower
support edge, its shifted-zeta logarithmic derivative is a Cauchy transform
of that edge restriction plus a holomorphic remainder. -/
def claim15510_shiftedZetaLogDerivativeEdgeCauchy : Prop :=
  ∀ (μ : SignedMeasure ℝ) (a : ℝ),
    finiteCompactSignedMeasure μ →
      IsLeast μ.variation.support a →
        ∀ logZeta : ℂ → ℂ,
          zetaLogBranch logZeta →
            ∃ ε : ℝ, 0 < ε ∧
              ∃ H : ℂ → ℂ,
                AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) ε) ∧
                  (∀ z : ℂ,
                    z ∈ Metric.ball (0 : ℂ) ε →
                      0 < z.re →
                        let s₀ : ℂ := (1 - a : ℝ)
                        let ν : SignedMeasure ℝ :=
                          translatedLowerEdge μ a ε
                        (-deriv (shiftedZetaExponential μ logZeta)
                            (s₀ + z)) /
                            shiftedZetaExponential μ logZeta (s₀ + z) =
                          signedComplexIntegral
                              (ν.restrict (Icc 0 ε))
                              (fun t : ℝ => (z + (t : ℂ))⁻¹) + H z)

end

end MathlibPlus.Open.ResearchFormalization.O0336
