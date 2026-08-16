import Mathlib

noncomputable section

open Filter
open MeasureTheory
open scoped BigOperators Topology

namespace MathlibPlus.Open.Analysis

/-- The primorial formed from the primes at most the finite depth `y`. -/
def primorialPrefix (y : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (y + 1)).filter Nat.Prime, p

/-- The Möbius coefficient used in the finite and all-prime kernels. -/
def mobiusReal (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℤ)

/-- The differentiated finite-depth kernel from the admitted statement. -/
def finitePrimeDepthKernel (y : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ (Nat.divisors (primorialPrefix y)), 
    mobiusReal d * ((d : ℝ) ^ 2)⁻¹ * Real.exp (-x / d)

/-- The differentiated all-prime kernel from the admitted statement. -/
def allPrimeKernel (x : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 0 < n},
    mobiusReal n.1 * ((n.1 : ℝ) ^ 2)⁻¹ * Real.exp (-x / n.1)

/-- The weighted square energies from the admitted statement. -/
def finitePrimeDepthEnergy (y : ℕ) (c : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    |finitePrimeDepthKernel y x| ^ (2 : ℕ) * Real.rpow x (2 * c - 1)

def allPrimeEnergy (c : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    |allPrimeKernel x| ^ (2 : ℕ) * Real.rpow x (2 * c - 1)

/-- Local uniform convergence on the nonnegative half-line. -/
def locallyUniformOnNonnegative
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ s : Set ℝ, IsCompact s → s ⊆ Set.Ici (0 : ℝ) →
    TendstoUniformlyOn F f atTop s

/--
The admitted local-convergence/norm-escape claim: the finite prime-depth
kernels converge locally uniformly, but their weighted Mellin energies escape
to infinity throughout `1 < c < 3/2`, so that convergence cannot be
interchanged with the noncompact weighted norm there.
-/
def primeDepthLocalConvergenceNormEscape : Prop :=
  locallyUniformOnNonnegative finitePrimeDepthKernel allPrimeKernel ∧
    ∀ c : ℝ, 1 < c → c < (3 / 2 : ℝ) →
      Tendsto (fun y : ℕ => finitePrimeDepthEnergy y c) atTop atTop ∧
        ¬Tendsto (fun y : ℕ => finitePrimeDepthEnergy y c) atTop
          (𝓝 (allPrimeEnergy c))

end MathlibPlus.Open.Analysis
