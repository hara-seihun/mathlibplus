import MathlibPlus.Open.ResearchFormalization.O0314Claim15341
import MathlibPlus.Open.Analysis.SymmetricDivisorFlux15335_15336

namespace MathlibPlus.Open.ResearchFormalization.O0314Claim15340

noncomputable section

/-- The completed true-line member of the symmetric divisor-relocation pair. -/
def completedLine15340 (b : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh (Real.pi * (s - (1 / 2 : ℂ))) *
      (((s - (1 / 2 : ℂ)) ^ 2 + (b : ℂ) ^ 2) ^ 2) /
    ((1 / 2 : ℂ) * s * (s - 1) *
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))

/-- The completed off-line member of the symmetric divisor-relocation pair. -/
def completedOff15340 (a b : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh (Real.pi * (s - (1 / 2 : ℂ))) *
      (((s - (1 / 2 : ℂ)) ^ 2 -
          ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2) *
        ((s - (1 / 2 : ℂ)) ^ 2 -
          ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2)) /
    ((1 / 2 : ℂ) * s * (s - 1) *
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))

def thetaPrime15340 (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re -
    (1 / 2 : ℝ) * Real.log Real.pi

/-- Away from boundary zeros, the completed symmetric divisor pair has equal
critical-line phase and the same normal flux and argument velocity. -/
def claim15340 : Prop :=
  ∀ (a b : ℝ),
    0 < a → a < 1 / 2 → 0 < b →
    ∀ t : ℝ,
      completedLine15340 b (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 →
      completedOff15340 a b (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 →
      Complex.arg
          (completedLine15340 b (1 / 2 + (t : ℂ) * Complex.I)) =
        Complex.arg
          (completedOff15340 a b (1 / 2 + (t : ℂ) * Complex.I)) ∧
      (deriv (fun s : ℂ => completedLine15340 b s)
          (1 / 2 + (t : ℂ) * Complex.I) /
          completedLine15340 b (1 / 2 + (t : ℂ) * Complex.I)).re =
        -thetaPrime15340 t ∧
      (deriv (fun s : ℂ => completedOff15340 a b s)
          (1 / 2 + (t : ℂ) * Complex.I) /
          completedOff15340 a b (1 / 2 + (t : ℂ) * Complex.I)).re =
        -thetaPrime15340 t ∧
      (deriv (fun u : ℝ =>
          completedLine15340 b (1 / 2 + (u : ℂ) * Complex.I)) t /
          completedLine15340 b (1 / 2 + (t : ℂ) * Complex.I)).im =
        -thetaPrime15340 t ∧
      (deriv (fun u : ℝ =>
          completedOff15340 a b (1 / 2 + (u : ℂ) * Complex.I)) t /
          completedOff15340 a b (1 / 2 + (t : ℂ) * Complex.I)).im =
        -thetaPrime15340 t

end
end MathlibPlus.Open.ResearchFormalization.O0314Claim15340
