import Mathlib
import MathlibPlus.Open.Research.BaezDuarte
import MathlibPlus.Open.Research.PochhammerCompactUniformDecay

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.AnalyticNumberTheory.BaezDuarteDyadicCriterion

private def criticalHalfPlane : Set ℂ :=
  {s : ℂ | (1 / 2 : ℝ) < s.re}

/-- The weighted half-open dyadic energy of the admitted Baez--Duarte
coefficient sequence. -/
private def dyadicEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico N (2 * N),
    Real.sqrt (k : ℝ) *
      |MathlibPlus.Open.Research.BaezDuarte.baezDuarteCoefficient k| ^ 2

/-- The epsilon-power bound with one implied constant for each epsilon. -/
private def dyadicEnergyCriterion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 1 ≤ N →
      dyadicEnergy N ≤ C * Real.rpow (N : ℝ) ε

/-- The forward coefficient estimate, with the constant independent of the
coefficient index. -/
private def coefficientDecay : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k →
      |MathlibPlus.Open.Research.BaezDuarte.baezDuarteCoefficient k| ≤
        C * Real.rpow (k : ℝ) (-3 / 4 + ε)

private def newtonPartial (m : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m,
    (MathlibPlus.Open.Research.BaezDuarte.baezDuarteCoefficient k : ℂ) *
      MathlibPlus.Open.Research.PochhammerCompactUniformDecay.pochhammer k (s / 2)

/-- Local uniform convergence of the Newton series to a holomorphic extension
of the reciprocal zeta function on the half-plane `Re s > 1/2`. -/
private def reciprocalZetaNewtonContinuation : Prop :=
  ∃ F : ℂ → ℂ,
    DifferentiableOn ℂ F criticalHalfPlane ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ criticalHalfPlane →
        TendstoUniformlyOn (fun m : ℕ => newtonPartial m) F Filter.atTop K) ∧
      (∀ s : ℂ, 1 < s.re → F s = (riemannZeta s)⁻¹)

/-- Claim 14135: the weighted dyadic energy criterion is equivalent to the
Riemann hypothesis; RH gives the stated coefficient decay, while the energy
bound yields local-uniform Newton convergence and the holomorphic continuation
of `1/ζ` on `Re s > 1/2`, whose functional-equation consequence is RH. -/
def claim14135 : Prop :=
  (RiemannHypothesis ↔ dyadicEnergyCriterion) ∧
    (RiemannHypothesis → coefficientDecay) ∧
    (dyadicEnergyCriterion →
      reciprocalZetaNewtonContinuation ∧ RiemannHypothesis)

end MathlibPlus.Open.AnalyticNumberTheory.BaezDuarteDyadicCriterion
