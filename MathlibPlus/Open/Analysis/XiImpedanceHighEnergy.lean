import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

/-- The Dirichlet-series form of the completed xi function on its absolutely
convergent half-plane, used at the high-energy arguments below. -/
noncomputable def xiZetaSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, if n = 0 then 0 else Complex.cpow (Complex.ofReal (n : ℝ)) (-s)

noncomputable def xi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
      Complex.cpow (Complex.ofReal Real.pi) (-s / 2) *
      Complex.Gamma (s / 2) * xiZetaSeries s

noncomputable def shiftedXi (z : ℂ) : ℂ :=
  xi ((1 / 2 : ℂ) + z)

noncomputable def zeroFrequencyFunction (x : ℝ) : ℂ :=
  deriv shiftedXi (Complex.ofReal (Real.sqrt x)) /
    (Complex.ofReal (Real.sqrt x) * shiftedXi (Complex.ofReal (Real.sqrt x)))

noncomputable def completedSigma (x : ℝ) : ℝ :=
  1 / 2 + Real.sqrt x

noncomputable def completedTau (t x : ℝ) : ℝ :=
  t / Real.sqrt x

noncomputable def completedPhase (t x : ℝ) : ℂ :=
  xi (Complex.ofReal (completedSigma x) +
      Complex.I * Complex.ofReal (completedTau t x)) /
    xi (Complex.ofReal (completedSigma x) -
      Complex.I * Complex.ofReal (completedTau t x))

noncomputable def cayleyImpedance (t x : ℝ) : ℂ :=
  (completedPhase t x - 1) /
    (Complex.I * Complex.ofReal t * (completedPhase t x + 1))

noncomputable def awayFromCayleyPoles (t : ℝ) : Filter ℝ :=
  Filter.atTop ⊓ Filter.principal
    {x : ℝ | (1 / 4 : ℝ) < x ∧ completedPhase t x ≠ -1}

/-- Claim 11276: the high-energy expansion of H. -/
def highEnergyZeroFrequencyAsymptotic : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ =>
      zeroFrequencyFunction x -
        Complex.ofReal
          ((Real.log x - 2 * Real.log (2 * Real.pi)) / (4 * Real.sqrt x)) -
        Complex.ofReal ((7 : ℝ) / (4 * x)))
    (fun x : ℝ => Complex.ofReal (Real.rpow x (-3 / 2 : ℝ)))

/-- Claim 11277: fixed-frequency impedance asymptotics away from its Cayley
poles, together with the stated leading equivalent and divergence. -/
def fixedFrequencyImpedanceAsymptotic : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    let l := awayFromCayleyPoles t
    Filter.NeBot l ∧
      Asymptotics.IsBigO l
        (fun x : ℝ => cayleyImpedance t x - zeroFrequencyFunction x)
        (fun x : ℝ =>
          Complex.ofReal
            ((1 + (Real.log x) ^ 3) / Real.rpow x (3 / 2 : ℝ))) ∧
      Asymptotics.IsEquivalent l
        (fun x : ℝ => Complex.ofReal x * cayleyImpedance t x)
        (fun x : ℝ => Complex.ofReal (Real.sqrt x * Real.log x / 4)) ∧
      Filter.Tendsto
        (fun x : ℝ => (Complex.ofReal x * cayleyImpedance t x).re)
        l Filter.atTop

end MathlibPlus.Open
