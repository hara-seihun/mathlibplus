import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

noncomputable section

/-- The primes not exceeding a natural cutoff. -/
def primeCutoff (y : ℕ) : Finset ℕ :=
  (Finset.Iic y).filter Nat.Prime

/-- The primorial attached to a natural prime cutoff. -/
def primorial (y : ℕ) : ℕ :=
  (primeCutoff y).prod id

/-- The finite Euler factor at the linear port. -/
def primeDensity (y : ℕ) : ℂ :=
  (primeCutoff y).prod (fun p => (1 : ℂ) - (p : ℂ)⁻¹)

/-- The port kernel used by the finite and all-prime sums. -/
def portKernel (x : ℂ) : ℂ :=
  Complex.exp (-x) - 1 + x

/-- The finite Möbius-exponential sum at a prime cutoff. -/
def finiteMöbiusExponential (y : ℕ) (t : ℂ) : ℂ :=
  ((primorial y).divisors).sum (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℂ) * Complex.exp (-((d : ℂ) * t)))

/-- The finite linear-port remainder. -/
def finitePort (y : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ (primeCutoff y).card * finiteMöbiusExponential y (x / (primorial y : ℂ)) +
    x * primeDensity y

/-- The all-prime Möbius limit at the linear port. -/
def allPrimePort (x : ℂ) : ℂ :=
  ∑' n : ℕ+, ((ArithmeticFunction.moebius (n : ℕ) : ℤ) : ℂ) *
    portKernel (x / (n : ℂ))

/-- The Mellin integral of the port kernel on the positive real axis. -/
def portKernelMellinIntegral (w : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    portKernel (t : ℂ) * Complex.cpow (t : ℂ) (-w - 1)

/-- The Mellin integral of the all-prime port on the positive real axis. -/
def allPrimePortMellinIntegral (w : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    allPrimePort (t : ℂ) * Complex.cpow (t : ℂ) (-w - 1)

/-- Claim 13394: quantitative compact convergence at every positive prime cutoff. -/
def quantitativeCompactConvergence_claim13394 : Prop :=
  ∀ y : ℕ, 2 ≤ y →
    ∀ X : ℝ, 0 ≤ X →
      ∀ x : ℂ, ‖x‖ ≤ X →
        ‖finitePort y x - allPrimePort x‖ ≤
            (y : ℝ) * (Real.exp (X / (y : ℝ)) - 1 - X / (y : ℝ)) ∧
          (y : ℝ) * (Real.exp (X / (y : ℝ)) - 1 - X / (y : ℝ)) ≤
            (X ^ 2 / (2 * (y : ℝ))) * Real.exp (X / (y : ℝ))

/-- Claim 13395: the RH-scale cutoff gives a uniform little-oh error. -/
def rhScaleDepthConsequence_claim13395 : Prop :=
  ∀ Y : ℝ → ℕ,
    Filter.Tendsto (fun X : ℝ => (Y X : ℝ) / X ^ (3 / 2 : ℝ)) Filter.atTop Filter.atTop →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ X : ℝ in Filter.atTop,
          ∀ x : ℂ, ‖x‖ ≤ X →
            ‖finitePort (Y X) x - allPrimePort x‖ ≤ ε * X ^ (1 / 2 : ℝ)

/-- Claim 13396: Mellin transform of the port kernel in its stated strip. -/
def mellinTransformPortKernel_claim13396 : Prop :=
  ∀ w : ℂ, 1 < w.re → w.re < 2 →
    portKernelMellinIntegral w = Complex.Gamma (-w)

/-- Claim 13397: reciprocal-zeta Mellin law in its stated strip. -/
def reciprocalZetaMellinLaw_claim13397 : Prop :=
  ∀ w : ℂ, 1 < w.re → w.re < 2 →
    allPrimePortMellinIntegral w = Complex.Gamma (-w) / riemannZeta w

end
end MathlibPlus.Open.Analysis
