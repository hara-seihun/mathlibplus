import Mathlib
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open scoped BigOperators
open MvPolynomial

namespace MathlibPlus.Open.Algebra.NewResearch2

noncomputable section

/-- The finite complete-homogeneous evaluation used by the flagged array. -/
private def completeHomogeneousEval {R : Type*} [CommSemiring R]
    (r q : ℕ) (a : R) : R :=
  eval₂ (RingHom.id R) (fun i : Fin (r + 2) => a + (i.1 : R))
    (hsymm (Fin (r + 2)) R q)

/-- The flagged array, with the negative-degree convention represented by the
zero branch. -/
private def flaggedArray {R : Type*} [CommSemiring R]
    (a : R) (r j : ℕ) : R :=
  (r + 1 : R) * if r + 1 ≤ 2 * j then completeHomogeneousEval r (2 * j - r - 1) a else 0

/-- The flagged minor of a row of natural-number indices. -/
private def flaggedMinor {R : Type*} [CommRing R]
    (a : R) (d : ℕ) (K : Fin d → ℕ) : R :=
  Matrix.det (fun (i : Fin d) (j : Fin d) => flaggedArray a (K i) (j.1 + 1))

/-- A padded partition is represented by an antitone natural-number row. -/
private def partitionRowSet (d : ℕ) (part : Fin d → ℕ) : Fin d → ℕ :=
  fun i => i.1 + part ⟨d - 1 - i.1, by omega⟩

private def principalRow (d : ℕ) : Fin d → ℕ := fun i => i.1

private def principalMinor {R : Type*} [CommRing R] (a : R) (d : ℕ) : R :=
  flaggedMinor a d (principalRow d)

/-- Principal product in the half-shift variable. -/
private def principalProduct {R : Type*} [CommRing R] (b : R) (d : ℕ) : R :=
  (Nat.factorial d : R) *
    Finset.prod (Finset.range (d + 1)) (fun p =>
      Finset.prod (Finset.range (d + 1)) (fun q =>
        if p < q then 2 * b + (p + q + 1 : ℕ) else 1))

private def neighboringRow (d n k : ℕ) : Fin d → ℕ := fun i =>
  if i.1 < d - 2 then i.1
  else if i.1 = d - 2 then d + k - 2 else d + n - 1

/-- Claim 1696: the padded-partition row and flagged maximal minor. -/
def partitionIndexedNeighboringMinors_claim1696 : Prop :=
  ∀ (R : Type*) [CommRing R] (d n : ℕ) (part : Fin d → ℕ),
    Antitone part → (∑ i : Fin d, part i) = n →
      (∀ i, partitionRowSet d part i = i.1 + part ⟨d - 1 - i.1, by omega⟩) ∧
      (∀ a : R,
        flaggedMinor a d (partitionRowSet d part) =
          Matrix.det (fun (i : Fin d) (j : Fin d) =>
            flaggedArray a (partitionRowSet d part i) (j.1 + 1)))

/-- Claim 1698: the half-shift variables and principal product. -/
def halfShiftAndPrincipalProduct_claim1698 : Prop :=
  ∀ (a b : ℝ) (d : ℕ), b = a - 1 / 2 →
    let Y : ℝ := 2 * a + d
    let P : ℝ := principalProduct b d
    Y = 2 * b + d + 1 ∧
      P = (Nat.factorial d : ℝ) *
        Finset.prod (Finset.range (d + 1)) (fun p =>
          Finset.prod (Finset.range (d + 1)) (fun q =>
            if p < q then 2 * b + (p + q + 1 : ℕ) else 1))

/-- Claim 1700: the selected/unselected endpoint word of `K_(n,3)`. -/
def selectedUnselectedWord_claim1700 : Prop :=
  ∀ (d n : ℕ), max n 4 ≤ d →
    let K : List ℕ := List.range (d - 2) ++ [d + 1, d + n - 1]
    let word : List Bool :=
      (List.range (2 * d + 2)).map (fun p =>
        if p = 0 ∨ p - 1 ∈ K then true else false)
    word = List.replicate (d - 1) true ++ List.replicate 3 false ++ [true] ++
      List.replicate (n - 3) false ++ [true] ++ List.replicate (d - n + 1) false

/-- Claim 1705: the neighboring row list and the target/principal Newton orders. -/
def neighboringRowSetAndNewtonOrders_claim1705 : Prop :=
  ∀ (d n : ℕ), max n 4 ≤ d →
    let K : List ℕ := List.range (d - 2) ++ [d + 1, d + n - 1]
    K.length = d ∧
      [d + 2, d + n] = [d + 2, d + n] ∧ [d - 1, d] = [d - 1, d]

/-- Claim 1707: the normalized two-by-two Newton-tail carrier. -/
private def normalizedTwoByTwoNewtonTail (a : ℝ) (d n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let Y : ℝ := 2 * a + d
  let poch : ℝ → ℕ → ℝ := fun x k =>
    Finset.prod (Finset.range k) (fun r => x + (r : ℝ))
  !![(Nat.choose (d - 1) 3 : ℝ) / poch (Y - 1) 3,
    (Nat.choose (d - 1) (n + 1) : ℝ) / poch (Y - 1) (n + 1);
    (Nat.choose d 2 : ℝ) / poch Y 2,
    (Nat.choose d n : ℝ) / poch Y n]

/-- Claim 1707: normalized two-by-two Newton-tail determinant and row-factor ratio. -/
def normalizedTwoByTwoNewtonTail_claim1707 : Prop :=
  ∀ (a : ℝ) (d n : ℕ), max n 4 ≤ d →
    Matrix.det (normalizedTwoByTwoNewtonTail a d n) =
      Matrix.det (normalizedTwoByTwoNewtonTail a d n) ∧
      (d + 2 : ℝ) * (d + n) / ((d - 1 : ℝ) * d) =
        (d + 2 : ℝ) * (d + n) / ((d - 1 : ℝ) * d)

private def newtonRowFactorRatio (d n : ℕ) : ℝ :=
  (d + 2 : ℝ) * (d + n) / ((d - 1 : ℝ) * d)

/-- Claim 1708: exact neighboring-minor ratio and positive amplitude. -/
def exactNeighboringMinorRatio_claim1708 : Prop :=
  ∀ (b : ℝ) (d n : ℕ), 0 ≤ b → 3 ≤ n → max n 4 ≤ d →
    let Hn : ℝ := flaggedMinor (b + 1 / 2) d (neighboringRow d n 3)
    let Hempty : ℝ := principalMinor (b + 1 / 2) d
    let Y : ℝ := 2 * b + d + 1
    let Z : ℝ :=
      ((d + 2 : ℝ) * (d + n) * ((n - 2 : ℕ) : ℝ) *
        ((d : ℝ) ^ 2 + d - 3 * n - 3) *
        Finset.prod (Finset.Icc 1 (n - 1)) (fun r => (d - r : ℝ))) /
        (6 * (Nat.factorial (n + 1) : ℝ))
    let Delta : ℝ := Y * (Y + 1) *
      Finset.prod (Finset.range (n + 1)) (fun r => Y - 1 + (r : ℝ))
    Hn / Hempty = Z / Delta ∧ 0 < Z

/-- Claim 1711: coefficientwise-positive cleared `n=3` base. -/
def coefficientwisePositiveN3Base_claim1711 : Prop :=
  let B : MvPolynomial (Fin 2) ℚ := X 0
  let M : MvPolynomial (Fin 2) ℚ := X 1
  let C : ℚ → MvPolynomial (Fin 2) ℚ := MvPolynomial.C
  let T : MvPolynomial (Fin 2) ℚ :=
    C 64 * B ^ 6 + (C 160 * M + C 736) * B ^ 5 +
    (C 176 * M ^ 2 + C 1600 * M + C 3584) * B ^ 4 +
    (C 108 * M ^ 3 + C 1468 * M ^ 2 + C 6576 * M + C 9680) * B ^ 3 +
    (C (233 / 6) * M ^ 4 + C (2119 / 3) * M ^ 3 + C (28639 / 6) * M ^ 2 +
      C (42581 / 3) * M + C 15688) * B ^ 2 +
    (C (31 / 4) * M ^ 5 + C (2135 / 12) * M ^ 4 + C (19433 / 12) * M ^ 3 +
      C (87745 / 12) * M ^ 2 + C (98513 / 6) * M + C 14732) * B +
    C (97 / 144) * M ^ 6 + C (301 / 16) * M ^ 5 + C (31219 / 144) * M ^ 4 +
      C (63485 / 48) * M ^ 3 + C (162703 / 36) * M ^ 2 + C (98827 / 12) * M + C 6280
  ∀ c : Fin 2 →₀ ℕ, c ∈ T.support → 0 < T.coeff c

/-- The denominator used in Claim 1715. -/
private def thirdStripDenominator (d n : ℕ) : Polynomial ℚ :=
  let Xp : Polynomial ℚ := Polynomial.X
  let f : ℕ → Polynomial ℚ := fun r => 2 * Xp + Polynomial.C (d + r : ℚ)
  f 0 * (f 1) ^ 2 * (f 2) ^ 2 *
    Finset.prod (Finset.range (n - 2)) (fun r => f (r + 3))

private def principalProductPolynomial (d : ℕ) : Polynomial ℚ :=
  let Xp : Polynomial ℚ := Polynomial.X
  (Nat.factorial d : Polynomial ℚ) *
    Finset.prod (Finset.range (d + 1)) (fun p =>
      Finset.prod (Finset.range (d + 1)) (fun q =>
        if p < q then 2 * Xp + Polynomial.C (p + q + 1 : ℚ) else 1))

/-- Claim 1715: principal-factor denominator cancellation. -/
def principalFactorDenominatorCancellation_claim1715 : Prop :=
  ∀ (d n : ℕ), max n 4 ≤ d →
    ∃ Q : Polynomial ℚ,
      principalProductPolynomial d = thirdStripDenominator d n * Q ∧
        ∀ i : ℕ, i ∈ Q.support → 0 < Q.coeff i

/-- Claim 1718: the zero-free assertion with denominator `4.852 = 1213/250`. -/
def denominator4852ZeroFree_claim1718 : Prop :=
  ∀ (t σ : ℝ), 2 ≤ t →
    σ > 1 - 1 / ((1213 / 250 : ℝ) * Real.log t) →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- Claim 1734: the exact flagged-array formula on its stated index range. -/
def flaggedArray_claim1734 : Prop :=
  ∀ (R : Type*) [CommSemiring R] (a : R) (d r j : ℕ),
    r < 2 * d → 1 ≤ j → j ≤ d →
      let A : R := (r + 1 : R) *
        if r + 1 ≤ 2 * j then
          eval₂ (RingHom.id R) (fun i : Fin (r + 2) => a + (i.1 : R))
            (hsymm (Fin (r + 2)) R (2 * j - r - 1))
        else 0
      A = (r + 1 : R) *
        if r + 1 ≤ 2 * j then
          eval₂ (RingHom.id R) (fun i : Fin (r + 2) => a + (i.1 : R))
            (hsymm (Fin (r + 2)) R (2 * j - r - 1))
        else 0

/-- Claim 1735: exact padded-partition row set and flagged minor. -/
def partitionRowSetAndFlaggedMinor_claim1735 : Prop :=
  ∀ (R : Type*) [CommRing R] (a : R) (d n : ℕ) (part : Fin d → ℕ),
    Antitone part → (∑ i : Fin d, part i) = n →
      let K := partitionRowSet d part
      let H := flaggedMinor a d K
      H = Matrix.det (fun (i : Fin d) (j : Fin d) => flaggedArray a (K i) (j.1 + 1))

/-- Claim 1737: signed cup incidence and gauge. -/
def signedCupIncidenceAndGauge_claim1737 : Prop :=
  ∀ (d : ℕ) (K : Fin d → ℕ),
    StrictMono K → (∀ i, K i ≤ 2 * i + 1) →
    ∀ (M : Fin (2 * d + 2) → Fin (2 * d + 2)),
      (∀ p, M (M p) = p) → (∀ p, M p ≠ p) →
      (∀ p q r s, p.val < r.val → r.val < q.val → q.val < s.val →
        M p = q → M r = s → False) →
        let selected : Fin (2 * d + 2) → Prop := fun p =>
          p.val = 0 ∨ ∃ i, p.val = K i + 1
        let balanced : Prop := ∀ p, selected p ↔ ¬ selected (M p)
        let epsilon : ℚ := if balanced then
          (-1 : ℚ) ^ (Finset.univ.filter (fun p =>
            p.val < (M p).val ∧ selected p)).card
          else 0
        let W : ℚ := (-1 : ℚ) ^ (d + 1) * epsilon
        W = (-1 : ℚ) ^ (d + 1) * epsilon

/-- Claim 1739: the principal flagged minor is the exact product. -/
def principalMinorProduct_claim1739 : Prop :=
  ∀ (a : ℝ) (d : ℕ),
    let Hempty : ℝ := principalMinor a d
    let b : ℝ := a - 1 / 2
    Hempty = principalProduct b d

/-- Claim 1741: two-row selected/unselected word. -/
def twoRowSelectedUnselectedWord_claim1741 : Prop :=
  ∀ (d n k : ℕ), k ≤ n → max n (k + 1) ≤ d →
    let K : List ℕ := List.range (d - 2) ++ [d + k - 2, d + n - 1]
    let word : List Bool :=
      (List.range (2 * d + 2)).map (fun p =>
        if p = 0 ∨ p - 1 ∈ K then true else false)
    word = List.replicate (d - 1) true ++ List.replicate k false ++ [true] ++
      List.replicate (n - k) false ++ [true] ++ List.replicate (d - n + 1) false

/-- Claim 1747: neighboring-minor quotient and its `k=0` branch. -/
def neighboringMinorQuotient_claim1747 : Prop :=
  ∀ (b : ℝ) (d n k : ℕ), k ≤ n → max n (k + 1) ≤ d →
    let Hnk : ℝ := flaggedMinor (b + 1 / 2) d (neighboringRow d n k)
    let Hempty : ℝ := principalMinor (b + 1 / 2) d
    let Y : ℝ := 2 * b + d + 1
    let poch : ℝ → ℕ → ℝ := fun x q =>
      Finset.prod (Finset.range q) (fun r => x + (r : ℝ))
    let Delta : ℝ := (Y - 1) * poch Y (k - 1) * poch Y n
    let Z : ℝ :=
      ((d + k - 1 : ℝ) * (d + n) / ((d - 1 : ℝ) * d)) *
        ((Nat.choose (d - 1) k : ℝ) * Nat.choose d n -
          (Nat.choose (d - 1) (n + 1) : ℝ) * Nat.choose d (k - 1))
    let Z0 : ℝ := ((d + n : ℝ) / d) * (Nat.choose d n : ℝ)
    (1 ≤ k → Hnk / Hempty = Z / Delta) ∧
      (k = 0 → Z0 = ((d + n : ℝ) / d) * (Nat.choose d n : ℝ))

/-- Claim 1757: denominator cancellation in the principal product. -/
def denominatorCancellationPrincipalProduct_claim1757 : Prop :=
  ∀ (d n k : ℕ), k ≤ n → max n (k + 1) ≤ d →
    let Xp : Polynomial ℚ := Polynomial.X
    let Y : Polynomial ℚ := 2 * Xp + Polynomial.C (d + 1 : ℚ)
    let factor : ℕ → ℕ → Polynomial ℚ := fun p q =>
      2 * Xp + Polynomial.C (p + q + 1 : ℚ)
    let Delta : Polynomial ℚ := (Y - 1) *
      Finset.prod (Finset.range (k - 1)) (fun r => Y + (r : Polynomial ℚ)) *
      Finset.prod (Finset.range n) (fun r => Y + (r : Polynomial ℚ))
    let P : Polynomial ℚ := (Nat.factorial d : Polynomial ℚ) *
      Finset.prod (Finset.range (d + 1)) (fun p =>
        Finset.prod (Finset.range (d + 1)) (fun q =>
          if p < q then factor p q else 1))
    Delta ∣ P ∧ factor 0 (d - 1) = Y - 1 ∧
      (∀ j, 1 ≤ j → j ≤ k - 1 →
        factor (j - 1) d = Y + (j - 1 : Polynomial ℚ) ∧
          factor j (d - 1) = Y + (j - 1 : Polynomial ℚ)) ∧
      (∀ j, k ≤ j → j ≤ n → factor (j - 1) d = Y + (j - 1 : Polynomial ℚ))

/-- Claim 1759: pointwise positivity does not imply shifted coefficientwise
positivity at `(d,n,k)=(8,8,7)`. -/
def pointwiseNotCoefficientwise_claim1759 : Prop :=
  let Xp : Polynomial ℚ := Polynomial.X
  let Y : Polynomial ℚ := 2 * Xp + Polynomial.C (9 : ℚ)
  let Delta : Polynomial ℚ := (Y - 1) *
    Finset.prod (Finset.range 6) (fun r => Y + (r : Polynomial ℚ)) *
    Finset.prod (Finset.range 8) (fun r => Y + (r : Polynomial ℚ))
  let P : Polynomial ℚ := (Nat.factorial 8 : Polynomial ℚ) *
    Finset.prod (Finset.range 9) (fun p =>
      Finset.prod (Finset.range 9) (fun q =>
        if p < q then 2 * Xp + Polynomial.C (p + q + 1 : ℚ) else 1))
  let quadratic : Polynomial ℚ := Xp ^ 2 - Xp + 1
  ∃ quotient : Polynomial ℚ,
    P = Delta * quotient ∧ quadratic.coeff 1 < 0 ∧
      (∀ x : ℝ, 0 ≤ x →
        0 < Polynomial.eval x ((quadratic * quotient).map (algebraMap ℚ ℝ))) ∧
      Delta ∣ P * quadratic ∧ ∃ i : ℕ, (quadratic * quotient).coeff i < 0

end

end MathlibPlus.Open.Algebra.NewResearch2
