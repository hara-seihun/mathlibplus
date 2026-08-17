import Mathlib
import MathlibPlus.Open.JacobsthalClaims
import MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083

namespace MathlibPlus.Open.ResearchFormalization.R1847.Claim32869

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The exact real base cutoff. -/
def realBaseCutoff (y : ℝ) : ℝ :=
  Real.sqrt (y / Real.log y)

/-- A base survivor set after one residue choice for each prime below `v`. -/
def baseSurvivorSet (y : ℝ)
    (c : MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.BaseChoice
      (Nat.floor y)) : Finset ℕ :=
  (Finset.range (Nat.floor y + 1)).filter
    (fun n =>
      ∀ p : MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.BasePrime
        (Nat.floor y),
        n % p.1 ≠ (c p).val)

/-- The finite tail prime set `v(y) < p ≤ w`. -/
def tailPrimes (y w : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor w + 1)).filter
    (fun p => Nat.Prime p ∧ realBaseCutoff y < (p : ℝ))

abbrev TailPrime (y w : ℝ) := {p : ℕ // p ∈ tailPrimes y w}

/-- One simultaneous selection of one tail residue class for each tail prime. -/
abbrev TailChoice (y w : ℝ) :=
  ∀ p : TailPrime y w, Fin p.1

/-- The tail sum against which the joint removable quantity is compared. -/
def tailSum (y w : ℝ) : ℝ :=
  ∑ p ∈ tailPrimes y w,
    (2 * y / (p : ℝ)) / Real.log (2 * y / (p : ℝ))

/-- The number removed from one fixed base survivor set by one simultaneous
choice of one residue class for every tail prime. -/
def jointlyRemovableCount (y w : ℝ)
    (c : MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.BaseChoice
      (Nat.floor y))
    (a : TailChoice y w) : ℕ :=
  ((baseSurvivorSet y c).filter
    (fun n => ∃ p : TailPrime y w, n % p.1 = (a p).val)).card

/-- The maximum over simultaneous tail residue choices of the size of the
union of the removable tail fibres. -/
def jointlyRemovableTail (y w : ℝ)
    (c : MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.BaseChoice
      (Nat.floor y)) : ℝ :=
  sSup (Set.range (fun a : TailChoice y w =>
    (jointlyRemovableCount y w c a : ℝ)))

/-- An eventual uniform joint saving by the exact maximum removable union. -/
def littleOAtTop (f : ℝ → ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds 0)

def uniformJointTailSaving (η : ℝ) : Prop :=
  ∃ e : ℝ → ℝ, littleOAtTop e ∧
    ∀ᶠ y : ℝ in Filter.atTop,
      ∀ w : ℝ, realBaseCutoff y ≤ w →
        ∀ c : MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.BaseChoice
          (Nat.floor y),
          jointlyRemovableTail y w c ≤
            (1 - η + e y) * tailSum y w

/-- The floor extension of the admitted lower-survivor quantity. -/
def logTwo (x : ℝ) : ℝ :=
  Real.log (Real.log x)

def survivorScale (x : ℝ) : ℝ :=
  x * logTwo x / (Real.log x) ^ 2

def realBaseSurvivorMinimum (y : ℝ) : ℝ :=
  MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.baseSurvivorMinimum
    (Nat.floor y)

def lowerSurvivorGain (δ : ℝ) : Prop :=
  ∃ e : ℝ → ℝ, littleOAtTop e ∧
    ∀ᶠ y : ℝ in Filter.atTop,
      (4 + δ + e y) * survivorScale y ≤
        realBaseSurvivorMinimum y

def jacobsthalGap (w : ℝ) : ℝ :=
  MathlibPlus.Open.JacobsthalClaims.primeResidueCoveringLength (Nat.floor w)

def eventuallyBigO (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ x : ℝ in Filter.atTop, |f x| ≤ C * |g x|

/-- Claim 32869: the dual saving uses the maximum of the simultaneous union
of tail residue fibres, and yields both stated exponent criteria. -/
def dualJointTailGain : Prop :=
  (∀ η : ℝ, 0 < η → η < 1 →
    uniformJointTailSaving η → lowerSurvivorGain 0 →
      ∀ c : ℝ, 0 < c → c < η / (1 - η) →
        (1 - η) * (1 + c) < 1 ∧
          eventuallyBigO jacobsthalGap
            (fun w => w ^ 2 / Real.rpow (Real.log w) c)) ∧
  (∀ ε : ℝ, 0 < ε → ε < 2 →
    uniformJointTailSaving (ε / 2) → lowerSurvivorGain 0 →
      ∀ c : ℝ, 0 < c → c < ε / (2 - ε) →
        eventuallyBigO jacobsthalGap
          (fun w => w ^ 2 / Real.rpow (Real.log w) c))

end

end MathlibPlus.Open.ResearchFormalization.R1847.Claim32869
