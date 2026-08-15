import Mathlib

namespace MathlibPlus.Open.Research.Batch_01a00468_ArithmeticKernels

noncomputable section
open scoped BigOperators
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The residual kernel from the local Euler factor. -/
abbrev PrimeNat := {q : ℕ // Nat.Prime q}

def residualKernel (k : ℕ) : ℝ :=
  if k = 0 then 0 else
    1 / ((k : ℝ) * ∏ q ∈ k.primeFactors, ((q + 1 : ℕ) : ℝ))

def residualMass : ℝ :=
  ∑' k : ℕ, if 1 ≤ k then residualKernel k else 0

def residualPrimeProduct : ℝ :=
  ∏' q : PrimeNat, (1 + 1 / ((q.1 : ℝ) ^ 2 - 1))

def residualInverseEulerProduct : ℝ :=
  ∏' q : PrimeNat, ((1 - 1 / (q.1 : ℝ) ^ 2)⁻¹)

def zetaTwoReal : ℝ := (riemannZeta (2 : ℂ)).re

/-- Claim 7191: the residual kernel has total mass ζ(2). -/
def claim7191 : Prop :=
  residualMass = residualPrimeProduct ∧
  residualPrimeProduct = residualInverseEulerProduct ∧
  residualInverseEulerProduct = zetaTwoReal

def arithmeticMobius (n : ℕ) : ℤ := ArithmeticFunction.moebius n

def primeSupportContained (j k : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ j → q ∣ k

def radicalSupportedCount (k : ℕ) : ℕ :=
  (Finset.Icc 1 k).filter (fun j => primeSupportContained j k) |>.card

def divisorFloorSum (k : ℕ) : ℤ :=
  ∑ N ∈ (Finset.Icc 1 k).filter (fun N => Nat.Coprime N k),
    arithmeticMobius N * ((k / N : ℕ) : ℤ)

def coprimeDivisorInnerSum (k j : ℕ) : ℤ :=
  ∑ N ∈ (Nat.divisors j).filter (fun N => Nat.Coprime N k), arithmeticMobius N

/-- Claim 8217: switching the finite sums gives the radical-supported count. -/
def claim8217 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    divisorFloorSum k =
      ∑ j ∈ Finset.Icc 1 k, coprimeDivisorInnerSum k j ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ k →
      coprimeDivisorInnerSum k j =
        if primeSupportContained j k then 1 else 0) ∧
    divisorFloorSum k = (radicalSupportedCount k : ℤ)

end
end MathlibPlus.Open.Research.Batch_01a00468_ArithmeticKernels
