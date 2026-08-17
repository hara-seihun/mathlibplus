import Mathlib
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import MathlibPlus.Open.Research.FormalizationRows

open scoped BigOperators
open MvPolynomial

namespace MathlibPlus.Open.ResearchFormalization.C0102C0119

noncomputable section

/-- Complete-homogeneous evaluation used in the flagged array. -/
def completeHomogeneousEval {R : Type*} [CommSemiring R]
    (r q : ℕ) (a : R) : R :=
  eval₂ (RingHom.id R) (fun i : Fin (r + 2) => a + (i.1 : R))
    (hsymm (Fin (r + 2)) R q)

/-- The flagged array, with complete homogeneous degree zero below the diagonal. -/
def flaggedArray {R : Type*} [CommSemiring R]
    (a : R) (r j : ℕ) : R :=
  (r + 1 : R) *
    if r + 1 ≤ 2 * j then completeHomogeneousEval r (2 * j - r - 1) a else 0

/-- The row indexed via a padded partition. -/
def paddedPartitionRow (d : ℕ) (part : ℕ → ℕ) (i : Fin d) : ℕ :=
  i.1 + part (d - 1 - i.1)

/-- The flagged maximal minor on a natural row set. -/
def flaggedMinor {R : Type*} [CommRing R]
    (a : R) (d : ℕ) (K : Fin d → ℕ) : R :=
  Matrix.det (fun (i : Fin d) (j : Fin d) => flaggedArray a (K i) (j.1 + 1))

/-- The padded one-column partition. -/
def oneColumnPart (j : ℕ) (k : ℕ) : ℕ :=
  if k < j then 1 else 0

/-- The principal and one-column minors in the half-shift variable. -/
def principalMinor (b : ℝ) (d : ℕ) : ℝ :=
  flaggedMinor (b + 1 / 2) d (fun i => i.1)

def oneColumnMinor (b : ℝ) (d j : ℕ) : ℝ :=
  flaggedMinor (b + 1 / 2) d (paddedPartitionRow d (oneColumnPart j))

def realPochhammer (x : ℝ) (k : ℕ) : ℝ :=
  ∏ r ∈ Finset.range k, (x + (r : ℝ))

/-- Claim 1577: the exact one-column neighboring-minor ratio. -/
def claim1577 : Prop :=
  ∀ (b : ℝ) (d j : ℕ),
    0 ≤ j ∧ j ≤ d →
      let Y : ℝ := 2 * b + d + 1
      oneColumnMinor b d j / principalMinor b d =
        (Nat.choose (d + j) j : ℝ) /
          realPochhammer (Y - j + 1) j

/-- Claim 1578: the cleared row initial values and one-step recurrence. -/
def claim1578 : Prop :=
  (∀ (m b : ℝ),
    MathlibPlus.Open.Research.clearedQ 0 m b = 1 ∧
      MathlibPlus.Open.Research.clearedQ 1 m b = 2 * b) ∧
  (∀ (d n : ℕ) (m b : ℝ),
    2 ≤ n ∧ n ≤ d ∧ m = ((d - n : ℕ) : ℝ) →
      MathlibPlus.Open.Research.clearedQ n m b =
        (2 * b + m + 2 * (n : ℝ)) *
            MathlibPlus.Open.Research.clearedQ (n - 1) (m + 1) b +
          (-1 : ℝ) ^ n * (m + 2 * (n : ℝ)) *
            MathlibPlus.Open.Research.clearedRising (m + 1) (n - 1) /
              (Nat.factorial n : ℝ))

/-- The cleared column family with its admitted initial normalization and recurrence. -/
def clearedR : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, _, b => 2 * b
  | n + 2, m, b =>
      (2 * b + (m : ℝ) + 2) * clearedR (n + 1) (m + 1) b +
        (-1 : ℝ) ^ (n + 2) *
          (Nat.choose (m + 2 * (n + 2)) (n + 2) : ℝ)

/-- Claim 1581: the positive odd two-step column formula. -/
def claim1581 : Prop :=
  ∀ (n m : ℕ) (b : ℝ),
    3 ≤ n → Odd n →
      clearedR n m b =
        (2 * b + (m : ℝ) + 2) * (2 * b + (m : ℝ) + 3) *
            clearedR (n - 2) (m + 2) b +
          (1 / (n : ℝ)) *
            (Nat.choose (m + 2 * n - 1) (n - 1) : ℝ) *
            (2 * (n : ℝ) * b + (n - 1 : ℝ) * (m : ℝ))

/-- The half-shift polynomial variable and the exact polynomial flagged array. -/
def halfShift : Polynomial ℚ :=
  Polynomial.X + Polynomial.C (1 / 2 : ℚ)

def flaggedMinorPoly (d : ℕ) (K : Fin d → ℕ) : Polynomial ℚ :=
  flaggedMinor halfShift d K

def principalPoly (d : ℕ) : Polynomial ℚ :=
  flaggedMinorPoly d (fun i => i.1)

/-- Padded hook and near-hook partition rows. -/
def hookPart (i j k : ℕ) : ℕ :=
  if k = 0 then i else if k ≤ j then 1 else 0

def nearHookPart (i ell k : ℕ) : ℕ :=
  if k = 0 then i else if k = 1 then 2 else if k ≤ ell + 1 then 1 else 0

def hookRows (d i j : ℕ) : Fin d → ℕ :=
  paddedPartitionRow d (hookPart i j)

def nearHookRows (d i ell : ℕ) : Fin d → ℕ :=
  paddedPartitionRow d (nearHookPart i ell)

def hookPoly (d i j : ℕ) : Polynomial ℚ :=
  flaggedMinorPoly d (hookRows d i j)

def nearHookPoly (d i ell : ℕ) : Polynomial ℚ :=
  flaggedMinorPoly d (nearHookRows d i ell)

/-- The shifted polynomial `Y` and its rising products. -/
def yPoly (d : ℕ) : Polynomial ℚ :=
  2 * Polynomial.X + Polynomial.C ((d + 1 : ℕ) : ℚ)

def polyRising (x : Polynomial ℚ) (k : ℕ) : Polynomial ℚ :=
  ∏ r ∈ Finset.range k, (x + Polynomial.C (r : ℚ))

def deltaPoly (d n ell : ℕ) : Polynomial ℚ :=
  yPoly d * polyRising (yPoly d - Polynomial.C ((ell + 1 : ℕ) : ℚ))
    (n + ell + 1)

/-- The exact alternating strip observable `S_{i,ell}`. -/
def stripS (d i ell : ℕ) : Polynomial ℚ :=
  2 * hookPoly d i 0 +
    (Finset.Icc 1 (ell + 1)).sum (fun j =>
      (-1 : Polynomial ℚ) ^ j * hookPoly d i j) +
    (Finset.range (ell + 1)).sum (fun j =>
      (-1 : Polynomial ℚ) ^ j * nearHookPoly d i j)

/-- The alternating arm and its normalized value. -/
def armR (d n ell : ℕ) : Polynomial ℚ :=
  (Finset.Icc 2 n).sum (fun i => (-1 : Polynomial ℚ) ^ i * stripS d i ell)

def armT (d n ell : ℕ) : FractionRing (Polynomial ℚ) :=
  (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (deltaPoly d n ell) /
      algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (principalPoly d)) *
    algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (armR d n ell)

/-- The cleared strip observable `C_{i,ell}`. -/
def stripC (d i ell : ℕ) : FractionRing (Polynomial ℚ) :=
  (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (deltaPoly d i ell) /
      algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (principalPoly d)) *
    algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (stripS d i ell)

def stripE (d i ell : ℕ) : FractionRing (Polynomial ℚ) :=
  (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
      (yPoly d + Polynomial.C ((i - 1 : ℕ) : ℚ))) *
      stripC d (i - 1) ell - stripC d i ell

/-- A concrete coefficientwise-nonnegative polynomial representative of a
fractional polynomial expression. -/
def coeffwiseNonnegativeFraction
    (f : FractionRing (Polynomial ℚ)) : Prop :=
  ∃ p : Polynomial ℚ,
    algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) p = f ∧
      ∀ k : ℕ, 0 ≤ p.coeff k

/-- Claim 1870: the exact alternating-arm recurrences and their
coefficientwise nonnegativity, on the flagged-minor carrier. -/
def claim1870 : Prop :=
  ∀ (d ell : ℕ), 1 ≤ ell ∧ ell + 2 ≤ d →
    armT d 2 ell = stripC d 2 ell ∧
    (∀ n : ℕ, 2 ≤ n ∧ n ≤ d →
      armT d n ell =
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
          (yPoly d + Polynomial.C ((n - 1 : ℕ) : ℚ))) * armT d (n - 1) ell +
          (-1 : FractionRing (Polynomial ℚ)) ^ n * stripC d n ell) ∧
    (∀ n : ℕ, 2 ≤ n ∧ n ≤ d → Even n →
      coeffwiseNonnegativeFraction (stripC d n ell)) ∧
    armT d 3 ell = stripE d 3 ell ∧
    (∀ n : ℕ, 3 ≤ n ∧ n ≤ d →
      coeffwiseNonnegativeFraction (stripE d n ell)) ∧
    (∀ n : ℕ, 3 ≤ n ∧ n ≤ d → Odd n →
      armT d n ell =
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
          (yPoly d + Polynomial.C ((n - 1 : ℕ) : ℚ))) *
          (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
            (yPoly d + Polynomial.C ((n - 2 : ℕ) : ℚ))) *
          armT d (n - 2) ell + stripE d n ell) ∧
    (∀ n : ℕ, 2 ≤ n ∧ n ≤ d → coeffwiseNonnegativeFraction (armT d n ell))

end

end MathlibPlus.Open.ResearchFormalization.C0102C0119
