import MathlibPlus.Analysis.ReciprocalXi

open MeasureTheory

namespace MathlibPlus.Open.Analysis.FourierLawCumulativeChannels15145

noncomputable section

/-- The Fourier law for the actual completed-theta divisibility channels.  The
channel is formed from the shell family before its Fourier transform is taken;
the unnormalised `exp (-i * u * x)` kernel and the completed xi carrier are
therefore part of the statement rather than reconstructed from its right-hand
side. -/
def fourierLawForCumulativeChannels_claim15145 : Prop :=
  let f : ℕ → ℝ → ℝ := fun n u ↦
    Real.exp (u / 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  let phi : ℕ → ℝ → ℝ := fun n u ↦
    iteratedDeriv 2 (f n) u - (1 / 4 : ℝ) * f n u
  let Phi : ℝ → ℝ := fun u ↦ ∑' n : ℕ, phi (n + 1) u
  let Phi_q : ℕ → ℝ → ℝ := fun q u ↦
    ∑' n : ℕ, if q ∣ (n + 1) then phi (n + 1) u else 0
  let F_q : ℕ → ℝ → ℂ := fun q x ↦
    ∫ u : ℝ,
      Complex.exp (-Complex.I * ((u * x : ℝ) : ℂ)) * (Phi_q q u : ℂ)
  let X : ℝ → ℂ := fun x ↦
    MathlibPlus.Analysis.ReciprocalXi.xi
      ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)
  let L : ℕ → ℝ := fun q ↦ Real.log (q : ℝ)
  (∀ u : ℝ, Phi_q 1 u = Phi u) ∧
    ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ,
      F_q q x =
        ((Real.rpow (q : ℝ) (-1 / 2 : ℝ) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * (((x * L q : ℝ) : ℂ))) * X x

end

end MathlibPlus.Open.Analysis.FourierLawCumulativeChannels15145
