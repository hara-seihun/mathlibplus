import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The fixed reciprocal two-sheet exponent in Claim 7440. -/
def reciprocalTwoSheetExponent : ℝ := 5 / 4

/-- The two-sheet kernel used by the Boolean determinant expansion. -/
def reciprocalTwoSheetKernel (q l : ℝ) : ℝ :=
  Real.rpow l (-reciprocalTwoSheetExponent) * Real.exp (-q / l) +
    Real.rpow l reciprocalTwoSheetExponent * Real.exp (-q * l)

/-- The value of a Boolean sheet, with `false` representing `0` and `true` representing `1`. -/
def booleanValue (b : Bool) : ℝ :=
  if b = true then 1 else 0

/-- The spectral point selected in a column by a Boolean sheet choice. -/
def booleanSheetScale {r : ℕ} (l : Fin r → ℝ) (ε : Fin r → Bool) (j : Fin r) : ℝ :=
  Real.rpow (l j) (2 * booleanValue (ε j) - 1)

/-- The low-sheet columns, numbered from `1` as in the admitted statement. -/
def lowSheetColumns {r : ℕ} (ε : Fin r → Bool) : Finset (Fin r) :=
  Finset.univ.filter (fun j => ε j = false)

/-- The Boolean sheet magnitude in the determinant expansion. -/
def booleanSheetMagnitude {r : ℕ} (q l : Fin r → ℝ) (ε : Fin r → Bool) : ℝ :=
  Real.exp
      (reciprocalTwoSheetExponent *
        ∑ j : Fin r,
          (2 * booleanValue (ε j) - 1) * Real.log (l j)) *
    |Matrix.det (fun i j => Real.exp (-q i * booleanSheetScale l ε j))|

/-- The orientation character from the exact sorting parity. -/
def booleanOrientationCharacter (r : ℕ) (ε : Fin r → Bool) : ℝ :=
  (-1 : ℝ) ^
    (Nat.choose r 2 +
      (lowSheetColumns ε).sum (fun j => (j.1 + 1) - 1))

/-- The low sheets in even-numbered columns. -/
def lowEvenSheetColumns {r : ℕ} (ε : Fin r → Bool) : Finset (Fin r) :=
  (lowSheetColumns ε).filter (fun j => Even (j.1 + 1))

/--
The exact Boolean orientation character and determinant expansion of Claim 7440.
The first conjunct records the displayed character formula; the second records
that, up to the rank-dependent sign, only low sheets in even-numbered columns
reverse orientation.  The final equality is the exact determinant expansion.
-/
def booleanOrientationCharacterDeterminantExpansion7440 : Prop :=
  ∀ (r : ℕ) (q l : Fin r → ℝ),
    (∀ i, 0 < q i) →
    StrictMono q →
    (∀ j, 1 < l j) →
    StrictMono l →
    (∀ ε : Fin r → Bool,
      booleanOrientationCharacter r ε =
        (-1 : ℝ) ^
          (Nat.choose r 2 +
            (lowSheetColumns ε).sum (fun j => (j.1 + 1) - 1))) ∧
    (∀ ε : Fin r → Bool,
      booleanOrientationCharacter r ε =
        (-1 : ℝ) ^ Nat.choose r 2 *
          (-1 : ℝ) ^ (lowEvenSheetColumns ε).card) ∧
    Matrix.det (fun i j => reciprocalTwoSheetKernel (q i) (l j)) =
      ∑ ε : Fin r → Bool,
        booleanOrientationCharacter r ε * booleanSheetMagnitude q l ε

end MathlibPlus.Open.Analysis
