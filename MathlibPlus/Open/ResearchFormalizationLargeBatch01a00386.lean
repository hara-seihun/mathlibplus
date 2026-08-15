import Mathlib

open scoped BigOperators
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386

noncomputable section

/-- The weighted absolute sum from Claim 14241. -/
def claim14241 : Prop :=
  ∀ (A : Set ℝ) (c : A → ℤ),
    A.Countable →
    A.Nonempty →
    BddBelow A →
    (∀ α : A, c α ≠ 0) →
    ∀ p₀ : ℝ, 1 < p₀ →
      Summable (fun α : A =>
        ((|c α| : ℤ) : ℝ) * Real.rpow p₀ (-((α : ℝ) - sInf A))) →
      ∀ M : ℝ, sInf A ≤ M →
        Set.Finite {α : A | (α : ℝ) ∈ Set.Icc (sInf A) M}

/-- The reciprocal-shift summand used in Claim 14249. -/
def reciprocalShiftSummand (p₀ : ℝ) (c : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((|c n| : ℤ) : ℝ) * Real.rpow p₀ (-1 / ((n + 1 : ℕ) : ℝ))

/-- The accumulation and nonsummability assertion of Claim 14249. -/
def claim14249 : Prop :=
  (∀ (p₀ : ℝ) (c : ℕ → ℤ),
    1 < p₀ →
    (∀ n : ℕ, c n ≠ 0) →
      ¬ Summable (reciprocalShiftSummand p₀ c) ∧
      ¬ Tendsto (reciprocalShiftSummand p₀ c) atTop (nhds 0)) ∧
  Tendsto (fun n : ℕ => 1 - 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 1)

abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
abbrev PositiveIndex := {k : ℕ // 1 ≤ k}
abbrev PrimePowerIndex := PrimeIndex × PositiveIndex

def primeLogBaseTwo (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / Real.log 2

def primeBernoulliA (p k : ℕ) : ℝ :=
  (k : ℝ) * primeLogBaseTwo p - 1

def primeBernoulliQ (p k : ℕ) : ℝ :=
  Real.exp (-primeBernoulliA p k)

/-- The prime-power weights and their convergent total from Claim 14252. -/
def claim14252 : Prop :=
  let c : ℝ := 1 / Real.log 2
  (1 < c) ∧
  (∀ (p k : ℕ), Nat.Prime p → 1 ≤ k → 0 ≤ primeBernoulliA p k) ∧
  primeBernoulliA 2 1 = 0 ∧
  (∀ (p k : ℕ), Nat.Prime p → 1 ≤ k →
    primeBernoulliQ p k =
      Real.exp 1 * Real.rpow (p : ℝ) (-(k : ℝ) / Real.log 2)) ∧
  Summable (fun pk : PrimePowerIndex =>
    primeBernoulliQ pk.1.1 pk.2.1) ∧
  (∑' pk : PrimePowerIndex, primeBernoulliQ pk.1.1 pk.2.1) =
    Real.exp 1 *
      (∑' p : PrimeIndex,
        Real.rpow (p.1 : ℝ) (-c) /
          (1 - Real.rpow (p.1 : ℝ) (-c))) ∧
  Summable (fun p : PrimeIndex =>
    Real.rpow (p.1 : ℝ) (-c) /
      (1 - Real.rpow (p.1 : ℝ) (-c)))

def weightedVariationFactor (j : ℕ) (pk : PrimePowerIndex) : ℝ :=
  1 + primeBernoulliQ pk.1.1 pk.2.1 * Real.exp (j : ℝ)

def weightedVariationRoot (j : ℕ) : ℝ :=
  tprod (weightedVariationFactor j)

def weightedVariation (j : ℕ) : ℝ :=
  (weightedVariationRoot j) ^ 2

/-- Convergence of every weighted variation in Claim 14259. -/
def claim14259 : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    HasProd (weightedVariationFactor j) (weightedVariationRoot j)

/-- The dyadic Carleman escape in Claim 14260. -/
def claim14260 : Prop :=
  (∀ m : ℕ, primeBernoulliQ 2 (m + 1) = Real.exp (-(m : ℝ))) ∧
  (∀ j : ℕ, 1 ≤ j →
    Real.log (weightedVariation (2 * j)) ≥
      3 * (j : ℝ) * ((j : ℝ) + 1) ∧
    Real.rpow (weightedVariation (2 * j))
        (-1 / ((2 * j : ℕ) : ℝ)) ≤
      Real.exp (-3 * ((j : ℝ) + 1) / 2)) ∧
  Summable (fun j : ℕ =>
    if 1 ≤ j then
      Real.rpow (weightedVariation (2 * j))
        (-1 / ((2 * j : ℕ) : ℝ))
    else 0)

def explicitVariation (j : ℕ) : ℝ :=
  (Real.cosh (2 * Real.pi * (2 : ℝ) ^ (j + 1)) - 1) / 2

def explicitCarlemanBound (j : ℕ) : ℝ :=
  Real.rpow 8 (1 / ((2 * j : ℕ) : ℝ)) *
    Real.exp (-Real.pi * (2 : ℝ) ^ (2 * j + 1) / (j : ℝ))

/-- The exact variations and quantitative escape in Claim 14271. -/
def claim14271 : Prop :=
  (∀ j : ℕ, 1 ≤ j → 0 < explicitVariation j) ∧
  Summable (fun j : ℕ =>
    if 1 ≤ j then
      Real.rpow (explicitVariation (2 * j))
        (-1 / ((2 * j : ℕ) : ℝ))
    else 0) ∧
  (∀ j : ℕ, 1 ≤ j →
    Real.rpow (explicitVariation (2 * j))
        (-1 / ((2 * j : ℕ) : ℝ)) ≤ explicitCarlemanBound j)

def claim14314_pseudosimilar {V : Type*} (C : SimpleGraph V) (z z' : V) : Prop :=
  z ≠ z' ∧
    Nonempty (SimpleGraph.Iso (C.induce ({z}ᶜ)) (C.induce ({z'}ᶜ))) ∧
    ¬∃ e : SimpleGraph.Iso C C, e.toEquiv z = z'

def eightVertexEdge (i j : Fin 8) : Prop :=
  (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
  (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
  (i = 0 ∧ j = 6) ∨ (i = 6 ∧ j = 0) ∨
  (i = 0 ∧ j = 7) ∨ (i = 7 ∧ j = 0) ∨
  (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1) ∨
  (i = 1 ∧ j = 5) ∨ (i = 5 ∧ j = 1) ∨
  (i = 1 ∧ j = 7) ∨ (i = 7 ∧ j = 1) ∨
  (i = 2 ∧ j = 5) ∨ (i = 5 ∧ j = 2) ∨
  (i = 2 ∧ j = 6) ∨ (i = 6 ∧ j = 2) ∨
  (i = 3 ∧ j = 6) ∨ (i = 6 ∧ j = 3) ∨
  (i = 3 ∧ j = 7) ∨ (i = 7 ∧ j = 3) ∨
  (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
  (i = 5 ∧ j = 7) ∨ (i = 7 ∧ j = 5)

def graphDegree {V : Type*} (C : SimpleGraph V) (v : V) : ℕ :=
  Set.ncard (C.neighborSet v)

/-- The eight-vertex edge-list graph assertion of Claim 14321. -/
def claim14321 : Prop :=
  ∃ C : SimpleGraph (Fin 8),
    (∀ i j : Fin 8, C.Adj i j ↔ eightVertexEdge i j) ∧
    (∀ v : Fin 8, 2 ≤ graphDegree C v ∧ graphDegree C v ≤ 4) ∧
    graphDegree C 0 = 4 ∧
    graphDegree C 6 = 4 ∧
    claim14314_pseudosimilar C 0 6

def spectralShift {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Q - lam • (1 : Matrix (Fin d) (Fin d) ℝ)

def normalizedAdjugateVector {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (e : Fin d → ℝ) : Fin d → ℝ :=
  let M := spectralShift Q lam
  let w := (Matrix.adjugate M).mulVec e
  fun i => w i / dotProduct e w

def simpleEigenvalue {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (u : Fin d → ℝ) : Prop :=
  ∀ v : Fin d → ℝ, Q.mulVec v = lam • v → ∃ r : ℝ, v = r • u

/-- The normalized adjugate eigenvector identity of Claim 14901. -/
def claim14901 : Prop :=
  ∀ (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ) (lam₀ : ℝ)
    (u₀ e : Fin d → ℝ),
    Q = Q.transpose →
    Q.mulVec u₀ = lam₀ • u₀ →
    dotProduct u₀ u₀ = 1 →
    simpleEigenvalue Q lam₀ u₀ →
    dotProduct e u₀ ≠ 0 →
    (fun i => u₀ i / dotProduct e u₀) =
      normalizedAdjugateVector Q lam₀ e

def borderedMatrix {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ)
    (e a : Fin d → ℝ) : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ :=
  Matrix.fromBlocks
    (spectralShift Q lam)
    (fun i _ => e i)
    (fun _ j => a j)
    (fun _ _ => 0)

/-- The bordered determinant and normalized-functional identity of Claim 14904. -/
def claim14904 : Prop :=
  ∀ (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ) (lam₀ : ℝ)
    (e : Fin d → ℝ),
    (∀ a : Fin d → ℝ,
      Matrix.det (borderedMatrix Q lam₀ e a) =
        -dotProduct a ((Matrix.adjugate (spectralShift Q lam₀)).mulVec e)) ∧
    (Matrix.det (borderedMatrix Q lam₀ e e) ≠ 0 →
      ∀ (ℓ : Fin d → ℝ),
        dotProduct ℓ (normalizedAdjugateVector Q lam₀ e) =
          Matrix.det (borderedMatrix Q lam₀ e ℓ) /
            Matrix.det (borderedMatrix Q lam₀ e e))

def bandOneT (v : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  v 0 + Real.sqrt 2 * v 1 * Real.cos (2 * Real.pi * t)

def bandOneMatrix (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 2 * ω
      else Real.sqrt 2 * Real.sin (2 * Real.pi * ω) / Real.pi
    else if j = 0 then
      Real.sqrt 2 * Real.sin (2 * Real.pi * ω) / Real.pi
    else
      2 * ω * Real.cos (2 * Real.pi * ω) +
        Real.sin (2 * Real.pi * ω) / Real.pi

def bandOneK (v : Fin 2 → ℝ) (ω : ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..ω, bandOneT v t * bandOneT v (ω - t)

def matrix2x2 (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then a else b
    else if j = 0 then c else d

/-- The point-source quadratic form identity of Claim 14907. -/
def claim14907 : Prop :=
  ∀ (v : Fin 2 → ℝ) (ω : ℝ),
    bandOneK v ω = dotProduct v ((bandOneMatrix ω).mulVec v)

/-- The three source-event matrices of Claim 14908. -/
def claim14908 : Prop :=
  bandOneMatrix (1 / 2) = matrix2x2 1 0 0 (-1) ∧
  bandOneMatrix 1 = matrix2x2 2 0 0 2 ∧
  bandOneMatrix (1 / 4) =
    matrix2x2 (1 / 2) (Real.sqrt 2 / Real.pi)
      (Real.sqrt 2 / Real.pi) (1 / Real.pi)

def continuumGamma (A B : ℝ) : ℝ :=
  Real.arcosh ((A ^ 2 + B ^ 2) / (B ^ 2 - A ^ 2))

/-- The physical-interval continuum bound of Claim 14998. -/
def claim14998 : Prop :=
  ∀ (A B L : ℝ) (k d : ℕ),
    0 < A → A < B → 0 < L → 1 ≤ k →
    ∀ P : Polynomial ℝ, P.natDegree ≤ d → P.eval 0 = 1 →
      let γJ := continuumGamma A B
      γJ = 2 * Real.artanh (A / B) ∧
      sSup
          ((fun x : ℝ =>
              |P.eval (x ^ 2 / Real.rpow L ((1 : ℝ) / (k : ℝ)))|) ''
            Set.Icc A B) ≥
        1 / Real.cosh ((d : ℝ) * γJ)

def claim15346 : Prop :=
  ∀ t : ℝ,
    2 * ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-x) * (1 - Real.cos (t * x)) / x ∂volume =
      Real.log (1 + t ^ 2) ∧
    4 * ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-x) * Real.cos x * (1 - Real.cos (t * x)) / x ∂volume =
      Real.log ((t ^ 4 + 4) / 4)

def integerNumericallyAdmissible (k c : ℤ) : Prop :=
  0 < k ∧ 0 < c ∧ 12 ∣ k + c ∧ 5 * k ≥ c - 36 ∧ k ≤ 3 * c

def admissiblePairSet (a : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    (Finset.product (Finset.Icc 1 (12 * a - 1)) (Finset.Icc 1 (12 * a - 1))).filter
      (fun p =>
        integerNumericallyAdmissible (p.1 : ℤ) (p.2 : ℤ) ∧
        integerNumericallyAdmissible (p.2 : ℤ) (p.1 : ℤ) ∧
        p.1 + p.2 = 12 * a)

def reversalRepresentative (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 ≤ p.2 then p else (p.2, p.1)

/-- The coordinate-reversal criterion and counts of Claim 59945. -/
def claim59945 : Prop :=
  (∀ (k c : ℤ), integerNumericallyAdmissible k c →
    (integerNumericallyAdmissible c k ↔ c ≤ 3 * k)) ∧
  (∀ (a : ℕ), 0 < a →
    ∀ (k c : ℤ), 0 < k → 0 < c → k + c = 12 * (a : ℤ) →
      (integerNumericallyAdmissible k c ∧ integerNumericallyAdmissible c k ↔
        3 * (a : ℤ) ≤ k ∧ k ≤ 9 * (a : ℤ))) ∧
  (∀ (a : ℕ), 0 < a →
    (admissiblePairSet a).card = 6 * a + 1 ∧
    ((admissiblePairSet a).image reversalRepresentative).card = 3 * a + 1)

end
end MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386
