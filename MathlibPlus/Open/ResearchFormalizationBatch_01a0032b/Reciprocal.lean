import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Batch_01a0032b

noncomputable section

section ReciprocalSheets

/-- The two sheet exponents attached to a Boolean sheet choice. -/
def sheetMagnitude {r : ℕ} (l : Fin r → ℝ) (ε : Fin r → Bool) (j : Fin r) : ℝ :=
  l j ^ (if ε j then (1 : ℤ) else (-1 : ℤ))

def reciprocalKernelMatrix {r : ℕ} (a : ℝ) (q l : Fin r → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => l j ^ (-a) * Real.exp (-q i / l j) +
    l j ^ a * Real.exp (-q i * l j)

def sheetMagnitudeFactor {r : ℕ} (a : ℝ) (l : Fin r → ℝ) (ε : Fin r → Bool) : ℝ :=
  Real.exp (a * ∑ j : Fin r,
    (if ε j then (1 : ℝ) else (-1 : ℝ)) * Real.log (l j))

def sheetMinorMagnitude {r : ℕ} (a : ℝ) (q l : Fin r → ℝ) (ε : Fin r → Bool) : ℝ :=
  sheetMagnitudeFactor a l ε *
    |Matrix.det (fun i j => Real.exp (-q i * sheetMagnitude l ε j))|

/-- Claim 7438: the reciprocal two-sheet kernel and strictly positive sheet magnitudes. -/
def reciprocalTwoSheetKernelAndMagnitudes : Prop :=
  ∀ (r : ℕ) (q l : Fin r → ℝ),
    (∀ i, 0 < q i) → StrictMono q →
    (∀ j, 1 < l j) → StrictMono l →
    (∀ ε : Fin r → Bool, Function.Injective (sheetMagnitude l ε)) →
    (∀ ε : Fin r → Bool, 0 < sheetMinorMagnitude (5 / 4 : ℝ) q l ε) ∧
    reciprocalKernelMatrix (5 / 4 : ℝ) q l =
      (fun i j => l j ^ (-(5 / 4 : ℝ)) * Real.exp (-q i / l j) +
        l j ^ (5 / 4 : ℝ) * Real.exp (-q i * l j))

/-- Flip one Boolean sheet. -/
def flipSheet {r : ℕ} (j : Fin r) (ε : Fin r → Bool) : Fin r → Bool :=
  Function.update ε j (!(ε j))

def mixedSheetDifference {r : ℕ} (E : Finset (Fin r))
    (A : (Fin r → Bool) → ℝ) (η : Fin r → Bool) : ℝ :=
  ∑ s ∈ E.powerset,
    (-1 : ℝ) ^ s.card * A (fun j => if j ∈ s then !(η j) else η j)

def evenSheetColumns (r : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun j => j.1 % 2 = 1)

def evenBaseAssignments (r : ℕ) : Type :=
  {η : Fin r → Bool // ∀ j, j ∈ evenSheetColumns r → η j = true}

/-- Claim 7441: type-B alternation is the displayed mixed finite difference. -/
def mixedFiniteDifferenceForm : Prop :=
  ∀ (r : ℕ) (q l : Fin r → ℝ),
    let a : ℝ := 5 / 4
    let K := reciprocalKernelMatrix a q l
    let A := sheetMinorMagnitude a q l
    let E := evenSheetColumns r
    letI : Finite (evenBaseAssignments r) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype (evenBaseAssignments r) := Fintype.ofFinite _
    (-1 : ℝ) ^ Nat.choose r 2 * Matrix.det K =
      ∑ η : evenBaseAssignments r,
        mixedSheetDifference E A η.1

/-- The rank-two sheet minor used in the reflection ratio. -/
def rankTwoSheetMagnitude (q₁ q₂ t₁ t₂ : ℝ) (ε₁ ε₂ : Bool) : ℝ :=
  sheetMinorMagnitude (5 / 4 : ℝ)
    ![q₁, q₂] ![Real.exp t₁, Real.exp t₂] ![ε₁, ε₂]

/-- Claim 7442: the exact rank-two reciprocal-reflection ratio. -/
def rankTwoReciprocalReflectionRatio : Prop :=
  ∀ (q₁ q₂ t₁ t₂ : ℝ), 0 < q₁ → q₁ < q₂ → 0 < t₁ → t₁ < t₂ →
    rankTwoSheetMagnitude q₁ q₂ t₁ t₂ false true ≠ 0 ∧
    rankTwoSheetMagnitude q₁ q₂ t₁ t₂ true false /
      rankTwoSheetMagnitude q₁ q₂ t₁ t₂ false true =
      Real.exp ((5 / 2 : ℝ) * (t₁ - t₂)) *
        Real.exp ((q₁ + q₂) * (Real.sinh t₂ - Real.sinh t₁)) *
        (Real.sinh ((q₂ - q₁) * Real.sinh ((t₁ + t₂) / 2)) /
          Real.sinh ((q₂ - q₁) * Real.sinh ((t₂ - t₁) / 2)))

/-- Claim 7445: the rank-three four-edge curvature identity. -/
def rankThreeFourEdgeCurvatureIdentity : Prop :=
  ∀ (q l : Fin 3 → ℝ),
    let K := reciprocalKernelMatrix (5 / 4 : ℝ) q l
    let A := sheetMinorMagnitude (5 / 4 : ℝ) q l
    Matrix.det K =
      ∑ ε₁ : Bool, ∑ ε₃ : Bool,
        (A ![ε₁, false, ε₃] - A ![ε₁, true, ε₃])

end ReciprocalSheets

end

end MathlibPlus.Open.Batch_01a0032b
