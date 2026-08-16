import MathlibPlus.Open.Analysis.FormalizationBatchMellin

namespace MathlibPlus.Open.Analysis.FormalizationBatchMellin

open MeasureTheory
open Set

/-- The Mellin--Plancherel pairing identity for a fixed Mellin profile. -/
def mellinPlancherelTestPacketPairing : Prop :=
  ∀ (w : ℝ → ℝ) (N : ℝ) (h : ℝ → ℝ),
    smoothFixedProfile w →
    0 < N →
    ContDiff ℝ ⊤ h →
    HasCompactSupport h →
    Function.support h ⊆ Ioi (0 : ℝ) →
    let gamma : ℕ → ℝ → ℂ := fun n t =>
      ((⌊t / ((n + 1 : ℕ) : ℝ)⌋ : ℤ) : ℂ) -
        ((⌊t⌋ : ℤ) : ℂ) / ((n + 1 : ℕ) : ℂ)
    let f : ℝ → ℂ := fun t =>
      ∑' n : ℕ,
        (ArithmeticFunction.moebius (n + 1) : ℂ) *
          Complex.ofReal (w (((n + 1 : ℕ) : ℝ) / N)) * gamma n t
    let hN : ℝ → ℝ := fun t => Real.sqrt N * h (t / N)
    let A : ℂ → ℂ := fun s =>
      ∑' n : ℕ,
        (ArithmeticFunction.moebius (n + 1) : ℂ) *
          Complex.ofReal (w (((n + 1 : ℕ) : ℝ) / N)) *
          Complex.cpow (Complex.ofReal ((n + 1 : ℕ) : ℝ)) (-s)
    let Hh : ℂ → ℂ := fun s =>
      ∫ y in Ioi (0 : ℝ),
        Complex.ofReal (h y) *
          Complex.cpow (Complex.ofReal y) (-s - 1) ∂volume
    let line : ℝ → ℂ := fun t =>
      (1 / 2 : ℂ) + Complex.I * (t : ℂ)
    let pairH : (ℝ → ℂ) → (ℝ → ℂ) → ℂ := fun u v =>
      ∫ t in Ici (1 : ℝ), star (u t) * v t / (t : ℂ) ^ 2 ∂volume
    pairH (fun t => Complex.ofReal (hN t)) (fun t => f t - 1) =
      (1 / (2 * Real.pi : ℂ)) *
        ∫ t : ℝ,
          ((riemannZeta (line t) * (A (line t) - A 1) - 1) / line t) *
            Complex.cpow (Complex.ofReal N) (Complex.I * (t : ℂ)) *
            star (Hh (line t)) ∂volume

end MathlibPlus.Open.Analysis.FormalizationBatchMellin
