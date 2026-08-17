import Mathlib

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2632.Claim42992

noncomputable section

private noncomputable def besselJ42992 (j : ℕ) (y : ℝ) : ℝ :=
  ∑' k : ℕ,
    ((-1 : ℝ) ^ k * (y / 2) ^ (2 * k + j)) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (j + k) : ℝ))

def chernoffKernel42992 (r : ℕ) (x t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (r - 1) *
    Real.rpow (t / x) (((r - 1 : ℕ) : ℝ) / 2) *
      besselJ42992 (r - 1) (2 * Real.sqrt (x * t))

def poissonTransform42992 (S_f : ℕ → ℝ) (z : ℝ) : ℝ :=
  Real.exp (-z) *
    ∑' n : ℕ, S_f n * z ^ n / (Nat.factorial n : ℝ)

def derivative42992 (S_f : ℕ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  iteratedDeriv r (fun z : ℝ => poissonTransform42992 S_f z) x

def exteriorSquare42992 (S_f : ℕ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  derivative42992 S_f x r * derivative42992 S_f x (r + 2) -
    derivative42992 S_f x (r + 1) ^ 2

def exteriorChannel42992 (S_f : ℕ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  x ^ r / (Nat.factorial r : ℝ) *
    |exteriorSquare42992 S_f x r|

def fockChannel42992 (S_f : ℕ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  x ^ r / (Nat.factorial r : ℝ) *
    |derivative42992 S_f x r| ^ 2

def fockEnergy42992 (S_f : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' r : ℕ, fockChannel42992 S_f x r

def primeRange42992 (T : ℝ) : Finset ℕ :=
  Finset.Icc 1 (Nat.floor (Real.exp T))

def vonMangoldtWeight42992 (m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m / (m : ℝ)

def centeredDerivative42992 (S_f : ℕ → ℝ) (x : ℝ) (r X : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 X,
    vonMangoldtWeight42992 m * chernoffKernel42992 r x (Real.log (m : ℝ))) -
    ∫ t in Set.Icc (0 : ℝ) (Real.log (X : ℝ)),
      chernoffKernel42992 r x t

def poissonCharlierCarrier42992 (S_f : ℕ → ℝ) : Prop :=
  ∀ (x : ℝ), 0 < x → ∀ r : ℕ, 1 ≤ r →
    derivative42992 S_f x r =
      Filter.limUnder Filter.atTop
        (fun X : ℕ => centeredDerivative42992 S_f x r X)

def finiteDerivative42992 (S_f : ℕ → ℝ)
    (x : ℝ) (r : ℕ) (T : ℝ) : ℝ :=
  (∑ m ∈ primeRange42992 T,
    vonMangoldtWeight42992 m * chernoffKernel42992 r x (Real.log (m : ℝ))) +
      chernoffKernel42992 (r + 1) x T

def cutoff42992 (C x : ℝ) : ℝ :=
  C * x ^ (5 / 3 : ℝ) * (Real.log x) ^ 2

def restrictedOrder42992 (A x : ℝ) (r : ℕ) : Prop :=
  2 ≤ r ∧ (r : ℝ) ≤ A * x

def exteriorEnvelope42992 (S_f : ℕ → ℝ) (A x : ℝ) : ℝ :=
  sSup {y : ℝ |
    y = 0 ∨ ∃ r : ℕ, restrictedOrder42992 A x r ∧
      y = exteriorChannel42992 S_f x r}

def restrictedFockEnergy42992 (S_f : ℕ → ℝ) (A x : ℝ) : ℝ := by
  classical
  exact ∑ r ∈ Finset.range (Nat.floor (max 0 (A * x)) + 1),
    if restrictedOrder42992 A x r then fockChannel42992 S_f x r else 0

def exteriorRate42992 (S_f : ℕ → ℝ) (A : ℝ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => x⁻¹ * Real.log (1 + exteriorEnvelope42992 S_f A x))
    Filter.atTop

def fockRate42992 (S_f : ℕ → ℝ) (A : ℝ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => x⁻¹ *
      Real.log (1 + restrictedFockEnergy42992 S_f A x))
    Filter.atTop

def centeredMeasureKernel42992 (x : ℝ) (r : ℕ) (t u : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (chernoffKernel42992 r x t * chernoffKernel42992 (r + 2) x u +
      chernoffKernel42992 r x u * chernoffKernel42992 (r + 2) x t -
      2 * chernoffKernel42992 (r + 1) x t *
        chernoffKernel42992 (r + 1) x u)

def centeredDoubleIntegral42992 (T : ℝ)
    (phi : ℝ → ℝ → ℝ) : ℝ :=
  let P := primeRange42992 T
  (∑ m ∈ P, ∑ n ∈ P,
      vonMangoldtWeight42992 m * vonMangoldtWeight42992 n *
        phi (Real.log (m : ℝ)) (Real.log (n : ℝ))) -
    2 * (∑ m ∈ P,
      vonMangoldtWeight42992 m *
        (∫ u in Set.Icc (0 : ℝ) T, phi (Real.log (m : ℝ)) u)) +
    ∫ t in Set.Icc (0 : ℝ) T,
      ∫ u in Set.Icc (0 : ℝ) T, phi t u

def finiteDeterminant42992 (S_f : ℕ → ℝ)
    (x : ℝ) (r : ℕ) (T : ℝ) : ℝ :=
  centeredDoubleIntegral42992 T (centeredMeasureKernel42992 x r)

def finiteExteriorChannel42992 (S_f : ℕ → ℝ)
    (x : ℝ) (r : ℕ) (T : ℝ) : ℝ :=
  x ^ r / (Nat.factorial r : ℝ) *
    |finiteDeterminant42992 S_f x r T|

def finiteFockEnergy42992 (S_f : ℕ → ℝ)
    (x : ℝ) (r : ℕ) (T : ℝ) : ℝ :=
  x ^ r / (Nat.factorial r : ℝ) *
    |finiteDerivative42992 S_f x r T| ^ 2

def finiteExteriorEnvelope42992 (S_f : ℕ → ℝ)
    (A C x : ℝ) : ℝ :=
  sSup {y : ℝ |
    y = 0 ∨ ∃ r : ℕ, restrictedOrder42992 A x r ∧
      y = finiteExteriorChannel42992 S_f x r (cutoff42992 C x)}

def finiteFockEnergyEnvelope42992 (S_f : ℕ → ℝ)
    (A C x : ℝ) : ℝ := by
  classical
  exact ∑ r ∈ Finset.range (Nat.floor (max 0 (A * x)) + 1),
    if restrictedOrder42992 A x r then
      finiteFockEnergy42992 S_f x r (cutoff42992 C x) else 0

def finiteExteriorRate42992 (S_f : ℕ → ℝ)
    (A C : ℝ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => x⁻¹ *
      Real.log (1 + finiteExteriorEnvelope42992 S_f A C x))
    Filter.atTop

def finiteFockRate42992 (S_f : ℕ → ℝ)
    (A C : ℝ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => x⁻¹ *
      Real.log (1 + finiteFockEnergyEnvelope42992 S_f A C x))
    Filter.atTop

def uniformFinitePrimeTransfer42992
    (S_f : ℕ → ℝ) (A H C : ℝ) : Prop :=
  0 < A ∧ 0 < H ∧ 0 < C ∧
    ∀ᶠ x : ℝ in Filter.atTop,
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ A * x →
        |derivative42992 S_f x r -
            finiteDerivative42992 S_f x r (cutoff42992 C x)| ≤
          Real.exp (-H * x * Real.log x)

def riemannHypothesis42992 : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 →
    0 < ρ.re → ρ.re < 1 → ρ.re = (1 / 2 : ℝ)

def offLineZero42992 (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
    ρ.re ≠ (1 / 2 : ℝ)

def verifiedHeight42992 : ℝ := 3000175332800

def verifiedSlopeBound42992 : ℝ :=
  verifiedHeight42992⁻¹ ^ 2

def matchingSlope42992 (ρ : ℂ) : ℝ :=
  1 / ((ρ.re - 1) ^ 2 + ρ.im ^ 2)

def verifiedHeightStatement42992 : Prop :=
  ∀ ρ : ℂ, offLineZero42992 ρ →
    |ρ.im| > verifiedHeight42992 ∧
      0 < matchingSlope42992 ρ ∧
        matchingSlope42992 ρ < verifiedSlopeBound42992

def finiteTransferCriterion42992
    (S_f : ℕ → ℝ) (A C : ℝ) : Prop :=
  uniformFinitePrimeTransfer42992 S_f A 1 C →
    (riemannHypothesis42992 ↔ exteriorRate42992 S_f A = 0) ∧
      (riemannHypothesis42992 ↔ fockRate42992 S_f A = 0) ∧
        (riemannHypothesis42992 ↔ finiteExteriorRate42992 S_f A C = 0) ∧
          (riemannHypothesis42992 ↔ finiteFockRate42992 S_f A C = 0)

/-- Claim 42992: the verified height puts every false-RH matching slope below
`A₀`, and the determinant and positive-energy RH criteria survive that exact
restriction and the common finite literal-prime cutoff. -/
def claim_42992 : Prop :=
  verifiedHeightStatement42992 ∧
    ∀ (S_f : ℕ → ℝ), poissonCharlierCarrier42992 S_f →
      (riemannHypothesis42992 ↔
          exteriorRate42992 S_f verifiedSlopeBound42992 = 0) ∧
        (riemannHypothesis42992 ↔
          fockRate42992 S_f verifiedSlopeBound42992 = 0) ∧
        (∀ A H : ℝ, 0 < A → 0 < H →
          ∃ C : ℝ, 0 < C ∧
            uniformFinitePrimeTransfer42992 S_f A H C) ∧
        (∀ C : ℝ, 0 < C →
          uniformFinitePrimeTransfer42992
              S_f verifiedSlopeBound42992 1 C →
            finiteTransferCriterion42992
              S_f verifiedSlopeBound42992 C)

end

end MathlibPlus.Open.ResearchFormalization.R2632.Claim42992
