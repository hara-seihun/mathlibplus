import Mathlib
import MathlibPlus.Open.NewResearch2.ThetaKernel
import MathlibPlus.Open.NewResearch2.PrimeRenewal15246

open scoped BigOperators Interval Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis.ShellRenewalNymanBatch

noncomputable section

namespace ShellTranslation

open MathlibPlus.Open.NewResearch2.ThetaKernel

/-- The source-defined completed-theta shell, not an arbitrary function family. -/
def shellPhi (n : ℕ) (u : ℝ) : ℝ :=
  thetaShell n u

/-- Claim 15144: exact translation of the fixed completed-theta shell family. -/
def claim15144 : Prop :=
  ∀ (q m : ℕ), 1 ≤ q → 1 ≤ m →
    ∀ u : ℝ,
      shellPhi (q * m) u =
        (q : ℝ) ^ (-1 / 2 : ℝ) * shellPhi m (u + Real.log (q : ℝ))

end ShellTranslation

namespace ReflectedRenewal

open MathlibPlus.Open.NewResearch2.PrimeRenewal15246

abbrev RenewalSpace (P : Finset ℕ) :=
  PiLp 2 (fun _ : Finset (PrimeIndex P) => L2)

/-- The exact reflection `f(u) ↦ f(-u)` on the Lebesgue `L²` carrier. -/
noncomputable def reflectionOperator : L2 →L[ℂ] L2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x)
      (Measure.measurePreserving_neg (volume : Measure ℝ))).toContinuousLinearMap

/-- The reflected positive renewal operator. -/
def reflectedRenewalOperator (a C : ℝ) : L2 →L[ℂ] L2 :=
  (C : ℂ) • ContinuousLinearMap.id ℂ L2 +
    (1 / 2 : ℂ) •
      (translationOperator (Real.log a) +
        translationOperator (-Real.log a))

/-- The operator on a finite completed exterior/Hilbert cube induced
coordinatewise from an operator on `L²(ℝ)`. -/
def cubeLift (P : Finset ℕ) (A : L2 →L[ℂ] L2)
    (x : RenewalSpace P) : RenewalSpace P :=
  WithLp.toLp 2 (fun s => A (x s))

/-- The finite renewal differential on the completed finite cube, written in
its canonical subset basis. -/
def cubeDifferential (P : Finset ℕ) (x : RenewalSpace P) : RenewalSpace P :=
  WithLp.toLp 2 (fun s =>
    ∑ p ∈ s,
      koszulSign s p • primeEulerFace p.1 (x (s.erase p)))

/-- The bilateral Laplace multiplier of the reflected operator. -/
def laplaceMultiplier (a C : ℝ) (z : ℂ) : ℂ :=
  (C : ℂ) + Complex.cosh (z * (Real.log a : ℂ))

/-- The two displayed off-axis zero branches. -/
def laplaceZero (a C : ℝ) (positive : Bool) (k : ℤ) : ℂ :=
  ((if positive then (Real.arcosh C : ℂ) else -(Real.arcosh C : ℂ)) +
      ((2 * (k : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)) /
    (Real.log a : ℂ)

/-- Claim 15247: the fixed unitary-translation renewal carrier admits a
positive invertible reflected operator whose bilateral multiplier has the
specified off-axis zeros, while the operator still commutes with the prime
faces, reflection, and every finite renewal cube. -/
def claim15247 : Prop :=
  ∀ (a C : ℝ), 1 < a → 1 < C →
    let A := reflectedRenewalOperator a C
    (A.IsPositive ∧
      (∃ B : L2 →L[ℂ] L2,
        B.comp A = ContinuousLinearMap.id ℂ L2 ∧
        A.comp B = ContinuousLinearMap.id ℂ L2)) ∧
    (∀ p : ℕ, Nat.Prime p →
      A.comp (primeEulerFace p) = (primeEulerFace p).comp A) ∧
    A.comp reflectionOperator = reflectionOperator.comp A ∧
    (∀ P : Finset ℕ, ∀ x : RenewalSpace P,
      cubeLift P A (cubeDifferential P x) =
        cubeDifferential P (cubeLift P A x)) ∧
    (∀ ξ : ℝ,
      (laplaceMultiplier a C ((ξ : ℂ) * Complex.I)).re =
        C + Real.cos (ξ * Real.log a)) ∧
    (∀ k : ℤ,
      laplaceMultiplier a C (laplaceZero a C true k) = 0 ∧
      laplaceMultiplier a C (laplaceZero a C false k) = 0 ∧
      (laplaceZero a C true k).re ≠ 0 ∧
      (laplaceZero a C false k).re ≠ 0)

end ReflectedRenewal

namespace NymanCyclicity

/-- The finite Dirichlet multiplier before any numerator inner divisor is
removed. -/
def dirichletMultiplier (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ S, c d * Complex.cpow (d : ℂ) (-s)

/-- The pole-cancelling value at `s=1`. -/
def poleCancellation (S : Finset ℕ) (c : ℕ → ℂ) : Prop :=
  ∑ d ∈ S, c d / (d : ℂ) = 0

/-- The removable value of `A_c(s)ζ(s)` at the cancelled zeta pole. -/
def centerValue (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ S, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

/-- The completed value of the raw multiplier times zeta, using the
removable value at the cancelled pole. -/
def rawZetaProduct (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then centerValue S c
  else dirichletMultiplier S c s * riemannZeta s

/-- The literal Nyman fractional-part function. -/
def nymanFunction (S : Finset ℕ) (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ d ∈ S,
    c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ)

/-- The critical Cauchy/Hardy energy of the raw product. -/
def hardyEnergy (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ t : ℝ,
      ‖rawZetaProduct S c ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 /
        (1 / 4 + t ^ 2)

/-- The exact unsquared literal Nyman `L²(0,1)` error. -/
def nymanError (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  Real.sqrt (
    ∫ x in Set.Ioo (0 : ℝ) 1,
      ‖(1 : ℂ) +
        nymanFunction S c x / centerValue S c‖ ^ 2)

/-- The normalized raw Hardy evaluation slack. -/
def rawSlack (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  hardyEnergy S c / ‖centerValue S c‖ ^ 2 - 1

/-- A finite positive-index coefficient vector with exact pole cancellation
and nonzero removable center value.  The raw product above is deliberately
used without an inner-divisor subtraction. -/
def validMultiplier (S : Finset ℕ) (c : ℕ → ℂ) : Prop :=
  (∀ d ∈ S, 1 ≤ d) ∧
    poleCancellation S c ∧
    centerValue S c ≠ 0

/-- Claim 15299: for every sequence of exact finite pole cancellers, the raw
Hardy slack tends to zero exactly when the corresponding literal unsquared
Nyman errors tend to zero; the coefficient vector is the only architecture
input. -/
def claim15299 : Prop :=
  ∀ (S : ℕ → Finset ℕ) (c : ℕ → ℕ → ℂ),
    (∀ j : ℕ, validMultiplier (S j) (c j)) →
      (∀ j : ℕ,
        hardyEnergy (S j) (c j) =
          ∫ x in Set.Ioo (0 : ℝ) 1,
            ‖nymanFunction (S j) (c j) x‖ ^ 2) ∧
      (∀ j : ℕ,
        rawSlack (S j) (c j) = nymanError (S j) (c j) ^ 2) ∧
      (Tendsto (fun j => rawSlack (S j) (c j)) atTop (𝓝 (0 : ℝ)) ↔
        Tendsto (fun j => nymanError (S j) (c j)) atTop (𝓝 (0 : ℝ)))

end NymanCyclicity

end

end MathlibPlus.Open.Analysis.ShellRenewalNymanBatch
