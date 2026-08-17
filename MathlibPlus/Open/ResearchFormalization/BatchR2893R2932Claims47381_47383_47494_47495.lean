import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR2893R2932

open scoped BigOperators

noncomputable section

/-- The two binary renewal coordinates from the finite binary support. -/
def renewalJ (q : ℕ) : ℕ :=
  (q.bitIndices.map (fun j => j * 2 ^ j)).sum

def renewalV (q : ℕ) : ℕ :=
  ∑ i ∈ Finset.range q, 2 ^ padicValNat 2 (i + 1)

def binaryRenewalStep (_q b : ℕ) : Prop :=
  b = 0 ∨ b = 1

/-- Claim 47381: the exact J/V identity and both binary recurrences. -/
def binaryRenewalCoordinates_claim47381 : Prop :=
  (∀ q : ℕ, renewalJ q = 2 * renewalV q - 2 * q) ∧
  (∀ q b : ℕ, binaryRenewalStep q b →
    renewalJ (2 * q + b) = 2 * renewalJ q + 2 * q ∧
      renewalV (2 * q + b) = 2 * renewalV q + q + b)

def normalFormEquation (n m q : ℕ) : Prop :=
  (n + m) * (q + 1) - renewalJ q = 2 ^ (m + 1) - 2

def normalFormSolution (n m q : ℕ) : Prop :=
  q < 2 ^ m ∧ normalFormEquation n m q

def minimalNormalFormCode (n q : ℕ) : Prop :=
  ∃ m : ℕ, normalFormSolution n m q ∧
    ∀ m' q', normalFormSolution n m' q' → q ≤ q'

/-- Claim 47383: odd codes are exactly the padding of shorter solutions,
minimal codes are even, and the consecutive support has q=0 and the displayed
length relation. -/
def renewalPaddingAndMinimalCode_claim47383 : Prop :=
  (∀ (n m q : ℕ), normalFormSolution n m q →
    normalFormSolution n (m + 1) (2 * q + 1)) ∧
  (∀ (n m q : ℕ), 1 ≤ m →
    normalFormSolution n (m + 1) (2 * q + 1) →
      normalFormSolution n m q) ∧
  (∀ (n m q' : ℕ), 1 ≤ m → normalFormSolution n (m + 1) q' →
    Odd q' → normalFormSolution n m ((q' - 1) / 2)) ∧
  (∀ n q : ℕ, minimalNormalFormCode n q → Even q) ∧
  (∀ m : ℕ, 1 ≤ m →
    normalFormSolution (2 ^ (m + 1) - m - 2) m 0)

def affineArea (a b : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + min (a ^ 2) (b ^ 2)

def affineCoefficientPair (a b : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ a + b = 1

def depthOneAtom₁ : ℝ × ℝ := (1, 0)
def depthOneAtom₂ : ℝ × ℝ := (0, 1)

def affineCombinationOfDepthOneAtoms
    (x : ℝ × ℝ) (a b : ℝ) : Prop :=
  affineCoefficientPair a b ∧
    x = (a * depthOneAtom₁.1 + b * depthOneAtom₂.1,
      a * depthOneAtom₁.2 + b * depthOneAtom₂.2)

def sublevelSet (c : ℝ) : Set (ℝ × ℝ) :=
  {x | affineArea x.1 x.2 ≤ c}

def firstQuadraticRegion (c : ℝ) : Set (ℝ × ℝ) :=
  {x | 2 * x.1 ^ 2 + x.2 ^ 2 ≤ c}

def secondQuadraticRegion (c : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ^ 2 + 2 * x.2 ^ 2 ≤ c}

/-- Claim 47494: the explicit F,G endpoints and their midpoint are depth-one
convex combinations, have the three displayed area values, and obey A≤1. -/
def affineBellmanNonQuasiconvexWitness_claim47494 : Prop :=
  let F : ℝ × ℝ := (5 / 12, 7 / 12)
  let G : ℝ × ℝ := (7 / 12, 5 / 12)
  let M : ℝ × ℝ := ((F.1 + G.1) / 2, (F.2 + G.2) / 2)
  affineCombinationOfDepthOneAtoms F (5 / 12) (7 / 12) ∧
    affineCombinationOfDepthOneAtoms G (7 / 12) (5 / 12) ∧
    affineArea F.1 F.2 = 11 / 16 ∧
    affineArea G.1 G.2 = 11 / 16 ∧
    M = (1 / 2, 1 / 2) ∧
    affineArea M.1 M.2 = 3 / 4 ∧
    (affineArea F.1 F.2 ≤ 1 ∧ affineArea G.1 G.2 ≤ 1 ∧
      affineArea M.1 M.2 ≤ 1) ∧
    affineArea M.1 M.2 > affineArea F.1 F.2

/-- Claim 47495: the exact natural two-region sublevel description. -/
def affineBellmanSublevelUnion_claim47495 : Prop :=
  (∀ c : ℝ, sublevelSet c =
    firstQuadraticRegion c ∪ secondQuadraticRegion c) ∧
  (∀ c : ℝ, ∀ x : ℝ × ℝ,
    affineArea x.1 x.2 ≤ c ↔
      2 * x.1 ^ 2 + x.2 ^ 2 ≤ c ∨
        x.1 ^ 2 + 2 * x.2 ^ 2 ≤ c) ∧
  ¬ (∀ c : ℝ, Convex ℝ (sublevelSet c))

end
end MathlibPlus.Open.ResearchFormalization.BatchR2893R2932
