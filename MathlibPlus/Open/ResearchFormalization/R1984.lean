import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1984

open scoped BigOperators

noncomputable section

abbrev PrimeNat := {p : ℕ // Nat.Prime p}

abbrev ProbabilityMeasure (R : Finset ℤ) :=
  {μ : {n // n ∈ R} → ℝ // (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x) = 1}

def residueMass (R : Finset ℤ) (μ : ProbabilityMeasure R)
    (p : PrimeNat) (a : ZMod p.1) : ℝ :=
  ∑ x : {n // n ∈ R}, if (x.1 : ZMod p.1) = a then μ.1 x else 0

def maxResidueMass (R : Finset ℤ) (μ : ProbabilityMeasure R)
    (p : PrimeNat) : ℝ := by
  classical
  letI : NeZero p.1 := ⟨Nat.Prime.ne_zero p.2⟩
  exact (Finset.univ.image (residueMass R μ p)).max' (by simp)

def fractionalAntiCoverLoad (R : Finset ℤ) (P : Finset PrimeNat)
    (μ : ProbabilityMeasure R) : ℝ :=
  P.sum (fun p => maxResidueMass R μ p)

def fractionalAntiCoverPhi (R : Finset ℤ) (P : Finset PrimeNat) : ℝ :=
  sInf (Set.range (fractionalAntiCoverLoad R P))

/-- The fractional anti-cover objective and its minimum over probability measures. -/
def fractionalAntiCoverObjective (R : Finset ℤ) (P : Finset PrimeNat) : Prop :=
  R.Nonempty ∧
    (∃ μ₀ : ProbabilityMeasure R,
      IsLeast (Set.range (fractionalAntiCoverLoad R P))
        (fractionalAntiCoverLoad R P μ₀) ∧
      fractionalAntiCoverPhi R P = fractionalAntiCoverLoad R P μ₀)

abbrev ResidueSimplex (p : PrimeNat) := ZMod p.1 → ℝ
abbrev DualFamily (P : Finset PrimeNat) := ∀ p : PrimeNat, ResidueSimplex p

def isResidueSimplex (p : PrimeNat) (lam : ResidueSimplex p) : Prop := by
  classical
  letI : NeZero p.1 := ⟨Nat.Prime.ne_zero p.2⟩
  exact (∀ a, 0 ≤ lam a) ∧ (∑ a, lam a) = 1

def isDualFamily (P : Finset PrimeNat) (lam : DualFamily P) : Prop :=
  ∀ p ∈ P, isResidueSimplex p (lam p)

def dualLoad (P : Finset PrimeNat) (lam : DualFamily P) (n : ℤ) : ℝ :=
  P.sum (fun p => lam p (n : ZMod p.1))

def dualMinimum (R : Finset ℤ) (P : Finset PrimeNat)
    (lam : DualFamily P) : ℝ := by
  classical
  by_cases hR : R.Nonempty
  · exact (R.image (dualLoad P lam)).min' (by simpa using hR)
  · exact 0

/-- The finite minimax identity for the fractional anti-cover objective. -/
def exactMinimaxDuality (R : Finset ℤ) (P : Finset PrimeNat) : Prop :=
  R.Nonempty ∧
    (∀ p, p ∈ P → Nat.Prime p.1) ∧
    (∃ lam₀ : DualFamily P,
      isDualFamily P lam₀ ∧
      fractionalAntiCoverPhi R P = dualMinimum R P lam₀ ∧
      ∀ lam : DualFamily P, isDualFamily P lam →
        dualMinimum R P lam ≤ dualMinimum R P lam₀)

end

end MathlibPlus.Open.ResearchFormalization.R1984
