import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-! Claim 11327: the projective identity with the algebraic logarithmic derivative. -/

def shiftedGammaC (s : ℂ) : ℂ :=
  Complex.cpow (Real.pi : ℂ) (-s / 2) * Complex.Gamma (6 + s / 2)

def shiftedGammaH (s : ℂ) : ℂ :=
  32 * (s - 1) * riemannZeta s /
    ((s + 2) * (s + 4) * (s + 6) * (s + 8) * (s + 10))

def shiftedGammaR (s : ℂ) : ℝ :=
  (deriv shiftedGammaC s / shiftedGammaC s).re

def projectiveS0 (s : ℂ) : ℂ :=
  iteratedDeriv 2 shiftedGammaH s

def projectiveS1 (s : ℂ) : ℂ :=
  -iteratedDeriv 2 shiftedGammaH s -
    2 * (shiftedGammaR s : ℂ) * deriv shiftedGammaH s

def projectiveS2 (s : ℂ) : ℂ :=
  iteratedDeriv 2 shiftedGammaH s +
    4 * (shiftedGammaR s : ℂ) * deriv shiftedGammaH s +
    4 * (shiftedGammaR s : ℂ) ^ 2 * shiftedGammaH s

def projectiveSigma (s : ℂ) : ℂ :=
  projectiveS0 s + 2 * projectiveS1 s + projectiveS2 s

def algebraicLogSecond (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  iteratedDeriv 2 f s / f s - (deriv f s / f s) ^ 2

def projectiveW (s : ℂ) : ℂ :=
  (deriv shiftedGammaH s / shiftedGammaH s + (shiftedGammaR s : ℂ)) /
    (shiftedGammaR s : ℂ)

def projectiveDelta (s : ℂ) : ℂ :=
  algebraicLogSecond shiftedGammaH s /
    (4 * (shiftedGammaR s : ℂ) ^ 2)

def projectivePortsIdentity : Prop :=
  ∀ (σ t : ℝ),
    shiftedGammaH ((σ : ℂ) - (t : ℂ) * Complex.I) ≠ 0 →
      let s : ℂ := (σ : ℂ) - (t : ℂ) * Complex.I
      (‖projectiveS0 s‖ ^ 2 + ‖projectiveS2 s‖ ^ 2 -
            2 * ‖projectiveS1 s‖ ^ 2) /
          ‖projectiveSigma s‖ ^ 2 =
        (projectiveW s).re ^ 2 + 2 * (projectiveDelta s).re

end MathlibPlus.Open.ResearchFormalizationBatch
