import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.O0315SlitRecurrenceSetup14106

noncomputable section

/-- Claim 14106: an exact slit-recurrence setup carries the closed disk,
its zero-free boundary and interior zeta-zero multiplicities, a parameterized
open boundary arc, and the recurrence event on the retained boundary. -/
def claim14106 : Prop :=
  ∃ (c : ℂ) (r T ε : ℝ) (m : ℕ),
    0 < r ∧
      0 < T ∧
      0 < m ∧
      let D := Metric.closedBall c r
      let Γ := Metric.sphere c r
      IsCompact D ∧
        IsSimplyConnected D ∧
        D ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re ∧ s.re < 1} ∧
        (∀ s ∈ Γ, riemannZeta s ≠ 0) ∧
        (∃ Z : Multiset ℂ,
          Z.card = m ∧
            (∀ z, z ∈ Z → z ∈ Metric.ball c r ∧ riemannZeta z = 0) ∧
            (∀ z : ℂ, z ∈ Metric.ball c r → riemannZeta z = 0 →
              ∀ k : ℕ,
                Multiset.count z Z = k ↔
                  ((∀ j < k, iteratedDeriv j riemannZeta z = 0) ∧
                    iteratedDeriv k riemannZeta z ≠ 0))) ∧
        0 < ε ∧
        ε < (1 / 4 : ℝ) *
          sInf {v : ℝ | ∃ s ∈ Γ, v = ‖riemannZeta s‖} ∧
        ∃ (J I K : Set ℂ) (a b : ℂ) (gamma : ℝ → ℂ) (A : Set ℝ),
          ContDiffOn ℝ 1 gamma (Set.Icc (0 : ℝ) 1) ∧
            Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, gamma t ∈ Γ) ∧
            J = gamma '' Set.Ioo (0 : ℝ) 1 ∧
            I = closure J ∧
            K = Γ \ J ∧
            a = gamma 0 ∧
            b = gamma 1 ∧
            (∃ ℓ : ℝ,
              0 < ℓ ∧
                ℓ = ∫ t in (0 : ℝ)..1, ‖deriv gamma t‖) ∧
            A = {τ : ℝ |
              T ≤ τ ∧
                τ ≤ 2 * T ∧
                  sSup
                      {v : ℝ |
                        ∃ s ∈ K,
                          v =
                            ‖riemannZeta (s + (τ : ℂ) * Complex.I) -
                              riemannZeta s‖} < ε}

end

end MathlibPlus.Open.ResearchFormalization.O0315SlitRecurrenceSetup14106
