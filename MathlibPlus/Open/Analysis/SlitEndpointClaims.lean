import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 14111: a zero-free slit completion has an endpoint logarithm jump. -/
def zeroFreeSlitEndpointLogJump : Prop :=
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
            (∀ z, z ∈ Metric.ball c r → riemannZeta z = 0 →
              ∀ k : ℕ,
                Multiset.count z Z = k ↔
                  ((∀ j < k, iteratedDeriv j riemannZeta z = 0) ∧
                    iteratedDeriv k riemannZeta z ≠ 0))) ∧
        0 < ε ∧
        ε < (1 / 4 : ℝ) *
          sInf {v : ℝ | ∃ s ∈ Γ, v = ‖riemannZeta s‖} →
      let q := ε / sInf {v : ℝ | ∃ s ∈ Γ, v = ‖riemannZeta s‖}
      let M_D :=
        sSup {v : ℝ | ∃ s ∈ Γ, v = ‖deriv riemannZeta s / riemannZeta s‖}
      q < (1 / 4 : ℝ) →
        ∃ c_D ell_D : ℝ,
          0 < c_D ∧
            0 < ell_D ∧
            ∀ (ell : ℝ) (J I K : Set ℂ) (a b : ℂ)
                (gamma : ℝ → ℂ) (tau : ℝ) (F : ℂ → ℂ) (U : Set ℂ),
              0 < ell →
                ell < ell_D →
                  ContDiffOn ℝ 1 gamma (Set.Icc (0 : ℝ) 1) ∧
                    Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
                    (∀ t ∈ Set.Icc (0 : ℝ) 1, gamma t ∈ Γ) ∧
                    J = gamma '' Set.Ioo (0 : ℝ) 1 ∧
                    I = closure J ∧
                    K = Γ \ J ∧
                    a = gamma 0 ∧
                    b = gamma 1 ∧
                    ell = ∫ t in (0 : ℝ)..1, ‖deriv gamma t‖ ∧
                    T ≤ tau ∧
                    tau ≤ 2 * T ∧
                    F = (fun s => riemannZeta (s + (tau : ℂ) * Complex.I)) ∧
                    IsOpen U ∧
                    D ⊆ U ∧
                    AnalyticOnNhd ℂ F U ∧
                    (∀ s ∈ U, F s ≠ 0) ∧
                    sSup {v : ℝ | ∃ s ∈ K, v = ‖F s - riemannZeta s‖} < ε →
                      ∃ L_F : ℂ → ℂ,
                        AnalyticOnNhd ℂ L_F D ∧
                          (∀ s ∈ D, Complex.exp (L_F s) = F s) ∧
                          ‖L_F b - L_F a‖ ≥
                            (2 : ℝ) * Real.pi * m -
                              2 * Real.arcsin q - M_D * ell ∧
                          ‖L_F b - L_F a‖ ≥ c_D

/-- Claim 14113: the exact dual norm of the prime-log endpoint functional. -/
def primeEndpointDualNorm : Prop :=
  ∀ (a_ell b_ell : ℂ),
    (1 / 2 : ℝ) < a_ell.re ∧
      a_ell.re < 1 ∧
      (1 / 2 : ℝ) < b_ell.re ∧
      b_ell.re < 1 →
      let P := {p : ℕ // Nat.Prime p}
      let H := {g : P → ℂ // Summable (fun p => ‖g p‖ ^ 2)}
      let Λ : H → ℂ := fun g =>
        ∑' p : P,
          g.1 p *
            ((p.1 : ℂ) ^ (-b_ell) - (p.1 : ℂ) ^ (-a_ell))
      let hnorm : H → ℝ := fun g =>
        Real.sqrt (∑' p : P, ‖g.1 p‖ ^ 2)
      let dualNorm : ℝ :=
        sSup {r : ℝ | ∃ g : H, hnorm g ≤ 1 ∧ r = ‖Λ g‖}
      dualNorm ^ 2 =
        ∑' p : P,
          ‖(p.1 : ℂ) ^ (-b_ell) - (p.1 : ℂ) ^ (-a_ell)‖ ^ 2

end MathlibPlus.Open.Analysis
