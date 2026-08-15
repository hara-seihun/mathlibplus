import Mathlib

noncomputable section
open scoped BigOperators
open Filter MeasureTheory Set
open Classical

namespace MathlibPlus.Open.FormalizationBatch.SetSystems

/-- The common finite-family sunflower carrier used by the admitted set-system claims. -/
def containsSunflower {α : Type} (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ G : Finset (Finset α),
    G ⊆ F ∧ G.card = r ∧
      ∃ C : Finset α,
        (∀ A ∈ G, C ⊆ A) ∧
        (∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = C)

def uniformFamily {α : Type} (F : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ A ∈ F, A.card = n

def LIntersectingFamily {α : Type}
    (F : Finset (Finset α)) (L : Finset ℕ) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ∈ L

def intersectionSpectrum {α : Type} (F : Finset (Finset α)) : Finset ℕ :=
  (F.product F).image (fun pair => (pair.1 ∩ pair.2).card)

def residualFamily {α : Type} (A : Finset α) (F : Finset (Finset α)) :
    Finset (Finset α) :=
  F.image (fun B => B \ A)

/-- Exact pivot residual identities and the non-increase of the spectrum. -/
def exactPivotResidualsDoNotIncreaseSpectrum : Prop :=
  ∀ {α : Type} (A T : Finset α) (F : Finset (Finset α)),
    (∀ B ∈ F, B ∩ A = T) →
      (∀ B ∈ F, ∀ C ∈ F,
        ((B \ A) ∩ (C \ A)).card = (B ∩ C).card - T.card) ∧
      (intersectionSpectrum (residualFamily A F)).card ≤
        (intersectionSpectrum F).card

def primeSetInterval (x : ℕ) : Finset ℕ :=
  (Finset.Icc (x + 1) (2 * x)).filter Nat.Prime

def residueCoordinate (p n : ℕ) : ℕ := n % p

def actualIntegerSetR (x M : ℕ) : Finset ℕ :=
  {0} ∪
    (primeSetInterval x).biUnion
      (fun p => (Finset.Icc 1 M).image (fun m => m * p))

def admissiblePrimeConstructionParameters (x M : ℕ) : Prop :=
  2 ≤ x ∧ 1 ≤ M ∧ M < x ∧ 2 * x * M < x ^ 2 ∧
    M + 1 ≥ (primeSetInterval x).card - 1

/-- The actual interval, distinct-prime, and residue-coordinate construction. -/
def actualIntervalAndDistinctPrimeConstruction : Prop :=
  ∀ x M : ℕ, admissiblePrimeConstructionParameters x M →
    actualIntegerSetR x M ⊆ Finset.range (x ^ 2) ∧
    ∀ p ∈ primeSetInterval x, ∀ n ∈ actualIntegerSetR x M,
      residueCoordinate p n = n % p

def distinctNonzeroPointsR (x M : ℕ) : Prop :=
  ∀ p q : ℕ, p ∈ primeSetInterval x → q ∈ primeSetInterval x → p ≠ q →
    ∀ m n : ℕ, m ∈ Finset.Icc 1 M → n ∈ Finset.Icc 1 M →
      m * p ≠ n * q

/-- Distinctness, cardinality, and interval containment of the actual set. -/
def distinctnessAndCardinalityOfActualSet : Prop :=
  ∀ x M : ℕ, admissiblePrimeConstructionParameters x M →
    distinctNonzeroPointsR x M ∧
    (actualIntegerSetR x M).card =
      1 + (primeSetInterval x).card * M ∧
    actualIntegerSetR x M ⊆ Finset.range (x ^ 2)

def residueFiber (R : Finset ℕ) (p r : ℕ) : Finset ℕ :=
  R.filter (fun n => n % p = r % p)

def zeroMultiplesBlock (p M : ℕ) : Finset ℕ :=
  {0} ∪ (Finset.Icc 1 M).image (fun m => m * p)

/-- Exact fibers, covering, and uniform largest-fiber objective. -/
def largestFibersAndExactCoverInActualInterval : Prop :=
  ∀ x M : ℕ, admissiblePrimeConstructionParameters x M →
    let P := primeSetInterval x
    let R := actualIntegerSetR x M
    (∀ p ∈ P, residueFiber R p 0 = zeroMultiplesBlock p M) ∧
    (∀ p q : ℕ, p ∈ P → q ∈ P → p ≠ q →
      ((Finset.Icc 1 M).image (fun n => (n * q) % p)).card = M) ∧
    (∀ p ∈ P, ∀ r : ℕ, 0 < r → r < p →
      (residueFiber R p r).card ≤ P.card - 1) ∧
    P.biUnion (fun p => residueFiber R p 0) = R ∧
    (∑ p ∈ P,
      ((residueFiber R p 0).card : ℝ) / (R.card : ℝ)) =
      ((P.card : ℝ) * (M + 1 : ℝ)) / (1 + (P.card * M : ℕ) : ℝ) ∧
    1 < ((P.card : ℝ) * (M + 1 : ℝ)) / (1 + (P.card * M : ℕ) : ℝ)

def criticalM (x : ℕ) : ℕ :=
  Nat.floor
    (2 * (x : ℝ) *
      (Real.log ((x : ℝ) ^ 2) / Real.log 2) /
      Real.log ((x : ℝ) ^ 2))

def criticalPrimeConstructionAsymptotics : Prop :=
  Asymptotics.IsEquivalent atTop
      (fun x : ℕ => ((primeSetInterval x).card : ℝ))
      (fun x : ℕ => (x : ℝ) / Real.log (x : ℝ)) ∧
    Asymptotics.IsEquivalent atTop
      (fun x : ℕ => ((actualIntegerSetR x (criticalM x)).card : ℝ))
      (fun x : ℕ =>
        4 * (x : ℝ) ^ 2 *
          (Real.log ((x : ℝ) ^ 2) / Real.log 2) /
          (Real.log ((x : ℝ) ^ 2)) ^ 2) ∧
    ∀ᶠ x : ℕ in atTop,
      admissiblePrimeConstructionParameters x (criticalM x)

/-- The fixed-intersection sunflower bound. -/
def fixedIntersectionSunflowerBound : Prop :=
  ∀ {α : Type} (L : Finset ℕ) (F : Finset (Finset α)) (n r : ℕ),
    uniformFamily F n → LIntersectingFamily F L →
    let s := L.card
    let M := max (r - 1) (n ^ 2 - n + 1)
    F.card > (s + 1) ^ n * M ^ s → containsSunflower F r

def boundedMaximumIntersectionHypothesis {α : Type}
    (F : Finset (Finset α)) (d : ℕ) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≤ d

def ordinaryDistinctUniformFamily {α : Type}
    (F : Finset (Finset α)) (n : ℕ) : Prop :=
  uniformFamily F n

def boundedMaximumIntersectionSunflowerBound : Prop :=
  ∃ C : ℝ, 1 < C ∧
    ∀ {α : Type} (F : Finset (Finset α)) (n r d : ℕ),
      3 ≤ n → 3 ≤ r → ordinaryDistinctUniformFamily F n →
      boundedMaximumIntersectionHypothesis F d →
      (F.card : ℝ) >
        (4 * (r : ℝ)) ^ n * C * r *
          (Real.log ((r * d : ℕ) : ℝ)) ^ d →
      containsSunflower F r

def fixedBaseLogarithmicSunflowerConsequence : Prop :=
  ∃ C : ℝ, 1 < C ∧
    ∀ {α : Type} (F : Finset (Finset α)) (n r d : ℕ) (γ : ℝ),
      3 ≤ n → 3 ≤ r → ordinaryDistinctUniformFamily F n →
      boundedMaximumIntersectionHypothesis F d →
      d * Real.log (C * r * Real.log ((r * d : ℕ) : ℝ)) ≤ γ * n →
      ¬ containsSunflower F r →
      (F.card : ℝ) ≤ (4 * (r : ℝ) * Real.exp γ) ^ n

def traceParameterSet (N : ℕ) : Finset ℕ :=
  Finset.range (Nat.floor (Real.sqrt (N : ℝ)) + 1)

def affinePronicTrace (B : ℤ) (N : ℕ) : Finset ℤ :=
  (traceParameterSet N).image
    (fun u => B + (u : ℤ) * ((u : ℤ) + 1))

def integerResidueFiber (S : Finset ℤ) (p : ℕ) (r : ℤ) : Finset ℤ :=
  S.filter (fun z => z % (p : ℤ) = r % (p : ℤ))

def quadraticRootsModulo (p : ℕ) (c : ZMod p) : Finset (Fin p) :=
  (Finset.univ : Finset (Fin p)).filter
    (fun u => (u.val : ZMod p) * (u.val + 1) = c)

/-- The quadratic root-count bound for small tail primes. -/
def quadraticRootCountBoundForSmallTailPrimes : Prop :=
  ∀ (N : ℕ) (B : ℤ) (p : ℕ), Nat.Prime p →
    (p : ℝ) ≤ 2 * Real.sqrt (N : ℝ) + 1 →
    (∀ r : ℤ,
      (integerResidueFiber (affinePronicTrace B N) p r).card ≤
        2 * (Real.sqrt (N : ℝ) + 1) / p + 2) ∧
    (∀ c : ZMod p, (quadraticRootsModulo p c).card ≤ 2)

/-- Injectivity and the one-point large-prime fibers. -/
def affinePronicInjectivityForLargeTailPrimes : Prop :=
  ∀ (N : ℕ) (B : ℤ) (p : ℕ), Nat.Prime p →
    (p : ℝ) > 2 * Real.sqrt (N : ℝ) + 1 →
    Set.InjOn
      (fun u : ℕ =>
        (B + (u : ℤ) * ((u : ℤ) + 1)) % (p : ℤ))
      (↑(traceParameterSet N) : Set ℕ) ∧
    (∀ r : ℤ,
      (integerResidueFiber (affinePronicTrace B N) p r).card ≤ 1)

def deltaSplitter {α : Type}
    (G : Finset (Finset α)) (δ : ℝ) (x : α) : Prop :=
  let s := G.card
  let d := (G.filter (fun A => x ∈ A)).card
  δ * s ≤ d ∧ d < s

def residualRestriction {α : Type}
    (F : Finset (Finset α)) (Q₁ Q₀ : Finset α) : Finset (Finset α) :=
  (F.filter (fun A => Q₁ ⊆ A ∧ A ∩ Q₀ = ∅)).image (fun A => A \ Q₁)

/-- Exact residual restrictions and the splitter definition. -/
def exactResidualRestrictionsAndSplitters : Prop :=
  (∀ {α : Type} (F : Finset (Finset α)) (n k : ℕ)
      (Q₁ Q₀ : Finset α),
    uniformFamily F n → ¬ containsSunflower F k → Q₁ ∩ Q₀ = ∅ →
    (residualRestriction F Q₁ Q₀).Nonempty →
      uniformFamily (residualRestriction F Q₁ Q₀) (n - Q₁.card) ∧
      ¬ containsSunflower (residualRestriction F Q₁ Q₀) k) ∧
  (∀ {α : Type} (G : Finset (Finset α)) (s : ℕ) (δ : ℝ) (x : α),
    G.card = s →
    (deltaSplitter G δ x ↔
      δ * s ≤ (G.filter (fun A => x ∈ A)).card ∧
        (G.filter (fun A => x ∈ A)).card < s))

end MathlibPlus.Open.FormalizationBatch.SetSystems
