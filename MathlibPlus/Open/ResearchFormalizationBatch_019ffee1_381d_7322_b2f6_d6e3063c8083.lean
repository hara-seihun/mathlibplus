import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/- The real-valued cutoff and its natural-number floor used to enumerate the
   primes in the finite base problem. -/
def baseCutoff (y : ℕ) : ℝ :=
  Real.sqrt ((y : ℝ) / Real.log (y : ℝ))

def baseCutoffNat (y : ℕ) : ℕ :=
  Nat.floor (baseCutoff y)

def basePrimes (y : ℕ) : Finset ℕ :=
  (Finset.range (baseCutoffNat y + 1)).filter Nat.Prime

abbrev BasePrime (y : ℕ) := {p : ℕ // p ∈ basePrimes y}

abbrev BaseChoice (y : ℕ) :=
  ∀ p : BasePrime y, Fin p.1

def baseSurvivorCount (y : ℕ) (c : BaseChoice y) : ℕ := by
  classical
  exact ((Finset.range (y + 1)).filter (fun n =>
    ∀ p : BasePrime y, n % p.1 ≠ (c p).val)).card

def baseSurvivorMinimum (y : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ c : BaseChoice y, baseSurvivorCount y c = m}

def basePrimorial (y : ℕ) : ℕ :=
  (basePrimes y).prod id

def shiftedSurvivorCount (y t : ℕ) : ℕ :=
  ((Finset.range (y + 1)).filter (fun n =>
    Nat.Coprime (t + n) (basePrimorial y))).card

def shiftedSurvivorMinimum (y : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ t : ℕ, shiftedSurvivorCount y t = m}

/-- Claim 32865: the residue-class minimum equals the CRT shift minimum. -/
def claim32865 : Prop :=
  ∀ y : ℕ, 2 ≤ y → baseSurvivorMinimum y = shiftedSurvivorMinimum y

/-- A finite probability distribution on a finite type. -/
def IsProbability {α : Type*} [Fintype α] (μ : α → ℝ) : Prop :=
  (∀ a, 0 ≤ μ a) ∧ ∑ a, μ a = 1

abbrev AntiCoverPoint (R : Finset ℕ) := {n : ℕ // n ∈ R}
abbrev AntiCoverPrime (P : Finset ℕ) := {p : ℕ // p ∈ P}


def residueOf (n : ℕ) (p : ℕ) (hp : 0 < p) : Fin p :=
  ⟨n % p, Nat.mod_lt n hp⟩

def residueMass {R P : Finset ℕ}
    (μ : AntiCoverPoint R → ℝ) (p : AntiCoverPrime P) (a : Fin p.1) : ℝ :=
  ∑ n : AntiCoverPoint R, if n.1 % p.1 = a.1 then μ n else 0

def residueMaximum {R P : Finset ℕ}
    (μ : AntiCoverPoint R → ℝ) (p : AntiCoverPrime P) : ℝ :=
  sSup (Set.range (fun a : Fin p.1 => residueMass μ p a))

def antiCoverPhi (R P : Finset ℕ) : ℝ :=
  sInf {x : ℝ |
    ∃ μ : AntiCoverPoint R → ℝ,
      IsProbability μ ∧
        x = ∑ p : AntiCoverPrime P, residueMaximum μ p}

def dualLoad {R P : Finset ℕ}
    (weights : ∀ p : AntiCoverPrime P, Fin p.1 → ℝ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (n : AntiCoverPoint R) : ℝ :=
  ∑ p : AntiCoverPrime P,
    weights p (residueOf n.1 p.1 (Nat.Prime.pos (hP p.1 p.2)))

def antiCoverDual (R P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) : ℝ :=
  sSup {x : ℝ |
    ∃ weights : ∀ p : AntiCoverPrime P, Fin p.1 → ℝ,
      (∀ p, IsProbability (weights p)) ∧
        x = sInf (Set.range (fun n : AntiCoverPoint R => dualLoad weights hP n))}

def HasIntegralAntiCover (R P : Finset ℕ) : Prop :=
  ∃ c : ∀ p : AntiCoverPrime P, Fin p.1,
    ∀ n : AntiCoverPoint R,
      ∃ p : AntiCoverPrime P, n.1 % p.1 = (c p).1

def IsPointMass {α : Type*} [Fintype α] (weights : α → ℝ) : Prop := by
  classical
  exact ∃ a : α, ∀ b, weights b = if b = a then 1 else 0

def IsPointMassFamily {P : Finset ℕ}
    (weights : ∀ p : AntiCoverPrime P, Fin p.1 → ℝ) : Prop :=
  ∀ p, IsPointMass (weights p)

def antiCoverPointMassLoads (R P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) : Prop :=
  ∃ weights : ∀ p : AntiCoverPrime P, Fin p.1 → ℝ,
    IsPointMassFamily weights ∧
      (∀ n : AntiCoverPoint R, 1 ≤ dualLoad weights hP n)

/-- Claim 32874: the finite fractional minimax identity, its integral-cover
    consequence, and the distinction between fractional and integral covers. -/
def claim32874 : Prop :=
  (∀ (R P : Finset ℕ), R.Nonempty →
    ∀ hP : ∀ p ∈ P, Nat.Prime p,
      antiCoverPhi R P = antiCoverDual R P hP ∧
      (antiCoverPhi R P < 1 → ¬ HasIntegralAntiCover R P) ∧
      (HasIntegralAntiCover R P ↔ antiCoverPointMassLoads R P hP)) ∧
  (∃ (R P : Finset ℕ), R.Nonempty ∧
    (∀ p ∈ P, Nat.Prime p) ∧
    1 ≤ antiCoverPhi R P ∧ ¬ HasIntegralAntiCover R P)

/- The larger-sieve quantities for a finite subset of the initial interval. -/
def sievePrimes (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter Nat.Prime

def fiberCount (R : Finset ℕ) (p a : ℕ) : ℕ :=
  (R.filter (fun n => n % p = a)).card

def fiberSquareSum (R : Finset ℕ) (p : ℕ) : ℝ :=
  ∑ a ∈ Finset.range p, (fiberCount R p a : ℝ) ^ 2

def fiberVariance (R : Finset ℕ) (p : ℕ) : ℝ :=
  fiberSquareSum R p - (R.card : ℝ) ^ 2 / (p : ℝ)

def sieveA (z : ℕ) : ℝ :=
  ∑ q ∈ sievePrimes z, Real.log (q : ℝ) / ((q : ℝ) - 1)

def sieveTheta (z : ℕ) : ℝ :=
  ∑ q ∈ sievePrimes z, Real.log (q : ℝ)

def sieveD (N p : ℕ) : ℝ :=
  Real.log (((max 1 ((N - 1) / p) : ℕ) : ℝ))

/-- Claim 32877: the displayed fiberwise larger-sieve inequality. -/
def claim32877 : Prop :=
  ∀ (R : Finset ℕ) (N z : ℕ),
    (∀ n ∈ R, n < N) →
    (∀ q ∈ sievePrimes z,
      ∃ a ∈ Finset.range q, ∀ n ∈ R, n % q ≠ a) →
    ∀ p : ℕ, z < p →
      fiberSquareSum R p = fiberVariance R p + (R.card : ℝ) ^ 2 / (p : ℝ) ∧
      (sieveA z - sieveD N p) * fiberSquareSum R p ≤
        (sieveTheta z - sieveD N p) * (R.card : ℝ)

end
end MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083
