import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ResearchPrimePhaseDisk

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

def nearEndpointPrime (c : ℝ) (p : ℕ) : Prop :=
  Nat.Prime p ∧ c - Real.rpow c (3 / 5 : ℝ) < (p : ℝ) ∧ (p : ℝ) < c

def endpointPrimes (c : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil c)).filter (nearEndpointPrime c)

def validReservedPrimes (c : ℝ) (reserve : Fin 4 → ℕ) : Prop :=
  Function.Injective reserve ∧ ∀ i : Fin 4, nearEndpointPrime c (reserve i)

def freeEndpointPrimes (c : ℝ) (reserve : Fin 4 → ℕ) : Finset ℕ :=
  (endpointPrimes c).filter (fun p => ∀ i : Fin 4, reserve i ≠ p)

def freePrimeRadius (c : ℝ) (reserve : Fin 4 → ℕ) : ℝ :=
  ∑ p ∈ freeEndpointPrimes c reserve, Real.rpow (p : ℝ) (-1 / 4 : ℝ)

def phaseImage (c : ℝ) (reserve : Fin 4 → ℕ) : Set ℂ :=
  {z | ∃ phase : {p // p ∈ freeEndpointPrimes c reserve} → ℂ,
    (∀ p, ‖phase p‖ = 1) ∧
      z = ∑ p, (Real.rpow (p.1 : ℝ) (-1 / 4 : ℝ) : ℂ) * phase p}

def closedComplexDisk (R : ℝ) : Set ℂ := {z | ‖z‖ ≤ R}

/-- Claim 2289: after any valid four-prime reservation, the remaining
prime-phase sums fill the disk of their total radius, and that radius has the
stated `c^(7/20)/log c` scale. -/
def freePrimePhaseDiskCapacity_claim2289 : Prop :=
  ∃ c₀ C₁ C₂ : ℝ, 0 < c₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
    ∀ c : ℝ, c₀ ≤ c →
      ∀ reserve : Fin 4 → ℕ, validReservedPrimes c reserve →
        phaseImage c reserve = closedComplexDisk (freePrimeRadius c reserve) ∧
        C₁ * Real.rpow c (7 / 20 : ℝ) / Real.log c ≤
          freePrimeRadius c reserve ∧
        freePrimeRadius c reserve ≤
          C₂ * Real.rpow c (7 / 20 : ℝ) / Real.log c

end
end MathlibPlus.Open.Analysis.ResearchPrimePhaseDisk
