import Mathlib

namespace MathlibPlus.Open.Research.BatchR5484

noncomputable section

open Polynomial

/- The integral polynomials and the trace coordinate used in Claim 60680. -/
def gPolynomial : Polynomial ℤ :=
  X ^ 5 + X ^ 4 - C 5 * X ^ 3 - C 5 * X ^ 2 + C 4 * X + C 4

def lPolynomial : Polynomial ℤ :=
  X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

def bPolynomial (a b c : ℤ) : Polynomial ℤ :=
  X ^ 10 + X ^ 9 - C (1 + c) * X ^ 7 - C (1 + b) * X ^ 6 -
    C (a + 2 * c) * X ^ 5 - C (1 + b) * X ^ 4 - C (1 + c) * X ^ 3 + X + 1

def traceQuintic (a b c : ℤ) : Polynomial ℤ :=
  gPolynomial - C a - C b * X - C c * X ^ 2

def complexPolynomial (p : Polynomial ℤ) : Polynomial ℂ :=
  p.map (Int.castRingHom ℂ)

def complexEvaluation (p : Polynomial ℤ) (z : ℂ) : ℂ :=
  (complexPolynomial p).eval z

def mahlerMeasure (p : Polynomial ℤ) : ℝ :=
  Polynomial.mahlerMeasure (complexPolynomial p)

def rootPowerSum (p : Polynomial ℤ) (k : ℕ) : ℂ :=
  Multiset.sum ((complexPolynomial p).roots.map (fun z => z ^ k))

def traceCoordinates (q : Polynomial ℤ) : Prop :=
  q.Monic ∧ q.natDegree = 5 ∧
    rootPowerSum q 1 = (-1 : ℂ) ∧ rootPowerSum q 2 = (11 : ℂ)

def reciprocalDegreeTen (p : Polynomial ℤ) : Prop :=
  p.Monic ∧ p.natDegree = 10 ∧ p.reverse = p ∧
    p.coeff 9 = 1 ∧ p.coeff 8 = 0

def measureOneTriple (a b c : ℤ) : Prop :=
  (a = -2 ∧ b = -2 ∧ c = 0) ∨
  (a = -1 ∧ b = -1 ∧ c = 0) ∨
  (a = 0 ∧ b = -2 ∧ c = -1) ∨
  (a = 0 ∧ b = 0 ∧ c = 0) ∨
  (a = 1 ∧ b = -2 ∧ c = -1) ∨
  (a = 2 ∧ b = -1 ∧ c = -1) ∨
  (a = 4 ∧ b = -2 ∧ c = -2) ∨
  (a = 4 ∧ b = 0 ∧ c = -1) ∨
  (a = 6 ∧ b = -3 ∧ c = -3) ∨
  (a = 8 ∧ b = -4 ∧ c = -4)

def lehmerTriple (a b c : ℤ) : Prop :=
  a = 1 ∧ b = 0 ∧ c = 0

def measureOneFactorizations : Prop :=
  bPolynomial (-2) (-2) 0 = Polynomial.cyclotomic 3 ℤ * Polynomial.cyclotomic 8 ℤ *
      Polynomial.cyclotomic 12 ℤ ∧
  bPolynomial (-1) (-1) 0 = Polynomial.cyclotomic 3 ℤ * Polynomial.cyclotomic 20 ℤ ∧
  bPolynomial 0 (-2) (-1) = Polynomial.cyclotomic 2 ℤ ^ 2 * Polynomial.cyclotomic 8 ℤ *
      Polynomial.cyclotomic 10 ℤ ∧
  bPolynomial 0 0 0 = Polynomial.cyclotomic 1 ℤ ^ 2 * Polynomial.cyclotomic 2 ℤ ^ 2 *
      Polynomial.cyclotomic 3 ℤ ^ 2 * Polynomial.cyclotomic 6 ℤ ∧
  bPolynomial 1 (-2) (-1) = Polynomial.cyclotomic 7 ℤ * Polynomial.cyclotomic 12 ℤ ∧
  bPolynomial 2 (-1) (-1) = Polynomial.cyclotomic 2 ℤ ^ 2 * Polynomial.cyclotomic 6 ℤ *
      Polynomial.cyclotomic 18 ℤ ∧
  bPolynomial 4 (-2) (-2) = Polynomial.cyclotomic 2 ℤ ^ 2 * Polynomial.cyclotomic 4 ℤ *
      Polynomial.cyclotomic 6 ℤ * Polynomial.cyclotomic 12 ℤ ∧
  bPolynomial 4 0 (-1) = Polynomial.cyclotomic 1 ℤ ^ 2 * Polynomial.cyclotomic 2 ℤ ^ 2 *
      Polynomial.cyclotomic 4 ℤ * Polynomial.cyclotomic 5 ℤ ∧
  bPolynomial 6 (-3) (-3) = Polynomial.cyclotomic 2 ℤ ^ 2 * Polynomial.cyclotomic 6 ℤ *
      Polynomial.cyclotomic 9 ℤ ∧
  bPolynomial 8 (-4) (-4) = Polynomial.cyclotomic 2 ℤ ^ 4 * Polynomial.cyclotomic 6 ℤ ^ 3

def claim60680 : Prop :=
  (∀ a b c : ℤ, ∀ z : ℂ, z ≠ 0 →
    complexEvaluation (bPolynomial a b c) z =
      z ^ 5 * (complexEvaluation gPolynomial (z + z⁻¹) - (a : ℂ) -
        (b : ℂ) * (z + z⁻¹) - (c : ℂ) * (z + z⁻¹) ^ 2)) ∧
  (∀ p : Polynomial ℤ,
    reciprocalDegreeTen p ↔ ∃ a b c : ℤ, p = bPolynomial a b c) ∧
  (∀ a b c : ℤ, traceCoordinates (traceQuintic a b c)) ∧
  (∀ a b c : ℤ, mahlerMeasure (bPolynomial a b c) = 1 ↔ measureOneTriple a b c) ∧
  measureOneFactorizations ∧
  bPolynomial 1 0 0 = lPolynomial ∧
  (∀ a b c : ℤ, mahlerMeasure (bPolynomial a b c) = mahlerMeasure lPolynomial ↔
    lehmerTriple a b c) ∧
  (∀ a b c : ℤ, (¬ measureOneTriple a b c ∧ ¬ lehmerTriple a b c) →
    mahlerMeasure lPolynomial < mahlerMeasure (bPolynomial a b c))

/- Substitution and root lifting used in Claim 60681. -/
def substitutedPolynomial (K : ℕ) (a b c : ℤ) : Polynomial ℤ :=
  (bPolynomial a b c).comp (X ^ K)

def substitutedLehmerPolynomial (K : ℕ) : Polynomial ℤ :=
  lPolynomial.comp (X ^ K)

def substitutedRootLifting (K : ℕ) (a b c : ℤ) : Prop :=
  (∀ z : ℂ,
    (complexPolynomial (substitutedPolynomial K a b c)).IsRoot z ↔
      (complexPolynomial (bPolynomial a b c)).IsRoot (z ^ K)) ∧
  (∀ r : ℂ, (complexPolynomial (bPolynomial a b c)).IsRoot r →
    Set.ncard {z : ℂ |
      (complexPolynomial (substitutedPolynomial K a b c)).IsRoot z ∧ z ^ K = r} = K)

def claim60681 : Prop :=
  ∀ K : ℕ, 1 ≤ K →
    (∀ a b c : ℤ,
      mahlerMeasure (substitutedPolynomial K a b c) = mahlerMeasure (bPolynomial a b c)) ∧
    (∀ a b c : ℤ, substitutedRootLifting K a b c) ∧
    (∀ a b c : ℤ, (substitutedPolynomial K a b c).natDegree = 10 * K) ∧
    (∀ a b c : ℤ, mahlerMeasure (substitutedPolynomial K a b c) = 1 ↔
      measureOneTriple a b c) ∧
    (∀ a b c : ℤ,
      mahlerMeasure (substitutedPolynomial K a b c) = mahlerMeasure lPolynomial ↔
        lehmerTriple a b c) ∧
    (∀ a b c : ℤ,
      (¬ measureOneTriple a b c ∧ ¬ lehmerTriple a b c) →
        mahlerMeasure lPolynomial < mahlerMeasure (substitutedPolynomial K a b c)) ∧
    substitutedPolynomial K 1 0 0 = substitutedLehmerPolynomial K ∧
    (∀ a b c : ℤ, (substitutedPolynomial K a b c).natDegree = 10 * K) ∧
    Irreducible (substitutedPolynomial K 1 0 0)

/- The trace shadow and its moment matrices used in Claim 60682. -/
def ellPolynomial : Polynomial ℤ :=
  X ^ 5 + X ^ 4 - C 5 * X ^ 3 - C 5 * X ^ 2 + C 4 * X + C 3

def traceChebyshevAux : ℕ → Polynomial ℤ × Polynomial ℤ
  | 0 => (C 2, X)
  | n + 1 =>
      let state := traceChebyshevAux n
      (state.2, X * state.2 - state.1)

def traceChebyshev (n : ℕ) : Polynomial ℤ :=
  (traceChebyshevAux n).1

def shadowPolynomial (K : ℕ) : Polynomial ℤ :=
  (ellPolynomial.comp (traceChebyshev K))

def shadowCyclotomicPolynomial (K : ℕ) : Polynomial ℤ :=
  shadowPolynomial K + 1

def traceN (K : ℕ) : ℕ := 5 * K

def realPolynomial (p : Polynomial ℤ) : Polynomial ℝ :=
  p.map (Int.castRingHom ℝ)

def realEvaluation (p : Polynomial ℤ) (x : ℝ) : ℝ :=
  (realPolynomial p).eval x

def traceRoots (p : Polynomial ℤ) : Multiset ℝ :=
  (realPolynomial p).roots

def qRoots (K : ℕ) : Multiset ℝ :=
  traceRoots (shadowPolynomial K)

def zRoots (K : ℕ) : Multiset ℝ :=
  traceRoots (shadowCyclotomicPolynomial K)

def qMoment (K j : ℕ) : ℝ :=
  Multiset.sum ((qRoots K).map (fun u => u ^ j))

def zMoment (K j : ℕ) : ℝ :=
  Multiset.sum ((zRoots K).map (fun v => v ^ j))

def qHankel (K r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j => qMoment K ((i : ℕ) + (j : ℕ))

def zHankel (K r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j => zMoment K ((i : ℕ) + (j : ℕ))

def qIntervalLocalizer (K r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j => 4 * qMoment K ((i : ℕ) + (j : ℕ)) -
    qMoment K ((i : ℕ) + (j : ℕ) + 2)

def zIntervalLocalizer (K r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j => 4 * zMoment K ((i : ℕ) + (j : ℕ)) -
    zMoment K ((i : ℕ) + (j : ℕ) + 2)

def tracePolynomialIdentities (K : ℕ) : Prop :=
  (∀ x : ℝ, x ≠ 0 →
    x ^ traceN K * realEvaluation (shadowPolynomial K) (x + x⁻¹) =
      realEvaluation lPolynomial (x ^ K)) ∧
  (∀ x : ℝ, x ≠ 0 →
    x ^ traceN K * realEvaluation (shadowCyclotomicPolynomial K) (x + x⁻¹) =
      (x ^ K - 1) ^ 2 * (x ^ K + 1) ^ 2 *
        (x ^ (2 * K) + x ^ K + 1) ^ 2 *
        (x ^ (2 * K) - x ^ K + 1))

def traceRootFacts (K : ℕ) : Prop :=
  Multiset.card (qRoots K) = traceN K ∧
  Multiset.card (zRoots K) = traceN K ∧
  (∀ v : ℝ, v ∈ zRoots K → -2 ≤ v ∧ v ≤ 2) ∧
  (∀ f : Polynomial ℝ, f.natDegree < traceN K →
    Multiset.sum ((qRoots K).map (fun u => f.eval u)) =
      Multiset.sum ((zRoots K).map (fun v => f.eval v)))

def tracePositivityFacts (K : ℕ) : Prop :=
  (∀ h p : Polynomial ℝ,
    (∀ x : ℝ, x ∈ Set.Icc (-2 : ℝ) 2 → 0 ≤ h.eval x) →
    (h * p ^ 2).natDegree < traceN K →
    Multiset.sum ((qRoots K).map (fun u => h.eval u * (p.eval u) ^ 2)) =
      Multiset.sum ((zRoots K).map (fun v => h.eval v * (p.eval v) ^ 2)) ∧
    0 ≤ Multiset.sum ((qRoots K).map (fun u => h.eval u * (p.eval u) ^ 2))) ∧
  (∀ r : ℕ, 2 * r < traceN K →
    qHankel K r = zHankel K r ∧
    Matrix.PosSemidef (qHankel K r) ∧ Matrix.PosSemidef (zHankel K r)) ∧
  (∀ r : ℕ, 2 * r + 2 < traceN K →
    qIntervalLocalizer K r = zIntervalLocalizer K r ∧
    Matrix.PosSemidef (qIntervalLocalizer K r) ∧
      Matrix.PosSemidef (zIntervalLocalizer K r)) ∧
  qMoment K (traceN K) - zMoment K (traceN K) = (traceN K : ℝ)

def claim60682 : Prop :=
  ∀ K : ℕ, 1 ≤ K →
    tracePolynomialIdentities K ∧ traceRootFacts K ∧ tracePositivityFacts K

/- The C7 x Q12 Cayley-CI claim, with C7 represented by the multiplicative
   wrapper around the additive cyclic group ZMod 7. -/
abbrev CayleyGroup := Multiplicative (ZMod 7) × QuaternionGroup 3

def rightCayleyAdjacency (S : Set CayleyGroup) (x y : CayleyGroup) : Prop :=
  ∃ s : CayleyGroup, s ∈ S ∧ y = x * s

def inverseClosed (S : Set CayleyGroup) : Prop :=
  ∀ x : CayleyGroup, x ∈ S → x⁻¹ ∈ S

def cayleyGraphIsomorphism (S T : Set CayleyGroup) : Prop :=
  ∃ e : CayleyGroup ≃ CayleyGroup,
    ∀ x y : CayleyGroup,
      rightCayleyAdjacency S x y ↔ rightCayleyAdjacency T (e x) (e y)

def claim60912 : Prop :=
  ∀ S T : Set CayleyGroup,
    (S ⊆ {x : CayleyGroup | x ≠ 1} ∧
      T ⊆ {x : CayleyGroup | x ≠ 1} ∧
      inverseClosed S ∧ inverseClosed T ∧
      ((Set.ncard S = 16 ∧ Set.ncard T = 16) ∨
        (Set.ncard S = 67 ∧ Set.ncard T = 67))) →
    cayleyGraphIsomorphism S T →
      ∃ α : CayleyGroup ≃* CayleyGroup, Set.image α S = T

end

end MathlibPlus.Open.Research.BatchR5484
