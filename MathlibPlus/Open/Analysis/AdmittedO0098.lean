import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable def hermiteEta (t : ℝ) : ℝ :=
  Real.pi * (2 * Real.pi * t ^ 4 - 3 * t ^ 2) * Real.exp (-Real.pi * t ^ 2) / 2

noncomputable def hermiteMellin (s : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.rpow t (s - 1) * hermiteEta t

/-- The ordinary seed moment is at the wrong exponent, including the critical
non-cancellation at zero frequency. -/
def ordinarySeedMomentWrongExponent : Prop :=
  hermiteMellin 1 = 0 ∧
    hermiteMellin (1 / 2) =
      -Real.Gamma (5 / 4) / (8 * Real.rpow Real.pi (1 / 4)) ∧
    hermiteMellin (1 / 2) ≠ 0 ∧
    (∀ σ : ℝ, 0 < σ → σ < 1 → hermiteMellin σ ≠ 0) ∧
    hermiteMellin 1 + hermiteMellin (1 / 2) ≠ 0

def primesUpTo (P : ℕ) : Finset ℕ :=
  (Finset.Icc 2 P).filter Nat.Prime

noncomputable def primeWeight (σ : ℝ) (q : ℕ) : ℝ :=
  Real.rpow (q : ℝ) (-σ)

noncomputable def mSigmaP (σ : ℝ) (P : ℕ) : ℝ :=
  ∏ q ∈ primesUpTo P, (1 - primeWeight σ q)⁻¹

noncomputable def aSigmaP (σ : ℝ) (P : ℕ) : ℝ :=
  ∑ q ∈ primesUpTo P,
    primeWeight σ q * Real.log (q : ℝ) / (1 - primeWeight σ q)

noncomputable def finiteTransferMultiplier (σ : ℝ) (P : ℕ) (ξ : ℝ) : ℂ :=
  ∏ q ∈ primesUpTo P,
    (1 - (primeWeight σ q : ℂ) *
      Complex.exp (Complex.I * (ξ : ℂ) * (Real.log (q : ℝ) : ℂ)))⁻¹

noncomputable def logarithmicSeed (σ x : ℝ) : ℂ :=
  (Real.exp (σ * x) * hermiteEta (Real.exp x) : ℂ)

def translateSeed (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f (x + a)

noncomputable def primeResolvent (σ : ℝ) (q : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∑' n : ℕ,
    (primeWeight σ q : ℂ) ^ n * f (x + (n : ℝ) * Real.log (q : ℝ))

noncomputable def finiteTransfer (σ : ℝ) (P : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (primesUpTo P).toList.foldl
    (fun g q => primeResolvent σ q g) f

noncomputable def transferEnergy (σ : ℝ) (P : ℕ) : ℝ :=
  ∫ x : ℝ, ‖finiteTransfer σ P (logarithmicSeed σ) x‖ ^ 2

noncomputable def complexMellinEta (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Complex.cpow (t : ℂ) (s - 1) * (hermiteEta t : ℂ)

noncomputable def logarithmicSeedFourierAmplitude (σ ξ : ℝ) : ℂ :=
  complexMellinEta ((σ : ℂ) - Complex.I * (ξ : ℂ))

/-- The local zero-frequency multiplier bound and its resulting energy lower
bound, with the transfer carrier and shrinking interval made explicit. -/
def shrinkingZeroFrequencyIntervalLowerBound : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 →
    ∃ Cσ : ℝ, 0 < Cσ ∧
      ∀ P : ℕ, 2 ≤ P →
        finiteTransferMultiplier σ P 0 = (mSigmaP σ P : ℂ) ∧
          (∀ ξ : ℝ,
            |ξ| ≤ 1 / (2 * aSigmaP σ P) →
              ‖finiteTransferMultiplier σ P ξ‖ ≥
                Real.exp (-1 / 2) * mSigmaP σ P) ∧
          transferEnergy σ P ≥
            Cσ * (mSigmaP σ P) ^ 2 / aSigmaP σ P

end MathlibPlus.Open.Analysis
