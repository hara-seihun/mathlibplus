import MathlibPlus.Open.ResearchFormalization.O0315SlitRecurrenceSetup14106

namespace MathlibPlus.Open.ResearchFormalization.O0315Claim14108

noncomputable section

/-- The retained-boundary quotient stays in the normalized q-disc, and its
endpoint principal arguments obey the corresponding arcsine bound. -/
def retainedBoundaryArgumentControl_claim14108 : Prop :=
  ∀ (c : ℂ) (r T ε : ℝ) (m : ℕ),
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
          sInf {v : ℝ | ∃ s ∈ Γ, v = ‖riemannZeta s‖} →
      let q := ε / sInf {v : ℝ | ∃ s ∈ Γ, v = ‖riemannZeta s‖}
      q < (1 / 4 : ℝ) →
        ∀ (J I K : Set ℂ) (a b : ℂ) (gamma : ℝ → ℂ)
          (ell tau : ℝ),
          ContDiffOn ℝ 1 gamma (Set.Icc (0 : ℝ) 1) ∧
            Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, gamma t ∈ Γ) ∧
            J = gamma '' Set.Ioo (0 : ℝ) 1 ∧
            I = closure J ∧
            K = Γ \ J ∧
            a = gamma 0 ∧
            b = gamma 1 ∧
            0 < ell ∧
            ell = ∫ t in (0 : ℝ)..1, ‖deriv gamma t‖ ∧
            T ≤ tau ∧
            tau ≤ 2 * T ∧
            sSup {v : ℝ |
              ∃ s ∈ K,
                v = ‖riemannZeta (s + (tau : ℂ) * Complex.I) -
                  riemannZeta s‖} ≤ ε →
          let F : ℂ → ℂ := fun s => riemannZeta (s + (tau : ℂ) * Complex.I)
          (∀ s ∈ K,
            ‖F s / riemannZeta s - 1‖ ≤ q) ∧
            |Complex.arg (F b / riemannZeta b) -
                Complex.arg (F a / riemannZeta a)| ≤
              2 * Real.arcsin q

end

end MathlibPlus.Open.ResearchFormalization.O0315Claim14108
