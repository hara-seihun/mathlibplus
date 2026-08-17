import Mathlib

noncomputable section

open Filter Topology

namespace MathlibPlus.Open.Research.FormalizationR0151

private def borderedFlag (m : ℕ) (B H : ℕ → ℝ) : ℝ :=
  Matrix.det (fun i j : Fin (m + 2) =>
    if j.val = m + 1 then B i.val else H (i.val + j.val))

private def capCofactor (m j : ℕ) (H : ℕ → ℝ) : ℝ :=
  borderedFlag m (fun n => if n = j then 1 else 0) H

/-- The coefficient sequence of the germ `cosh (√z)`. -/
private def coshSqrtCoefficients (n : ℕ) : ℝ :=
  1 / (Nat.factorial (2 * n) : ℝ)

/-- The coefficient sequence of the germ `cosh (y * √z)`. -/
private def atomicCapCoefficients (y : ℝ) (n : ℕ) : ℝ :=
  y ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

private def atomicFlag (m : ℕ) (y : ℝ) : ℝ :=
  borderedFlag m (atomicCapCoefficients y) coshSqrtCoefficients

/-- A sign wall is a zero across which the flag has opposite one-sided signs. -/
private def signChangesAt (f : ℝ → ℝ) (y : ℝ) : Prop :=
  f y = 0 ∧
    ∃ epsLeft epsRight : ℝ,
      0 < epsLeft ∧
      0 < epsRight ∧
      ((∀ x : ℝ, y - epsLeft < x → x < y → 0 < f x) ∧
        (∀ x : ℝ, y < x → x < y + epsRight → f x < 0) ∨
       (∀ x : ℝ, y - epsLeft < x → x < y → f x < 0) ∧
        (∀ x : ℝ, y < x → x < y + epsRight → 0 < f x))

private def firstPositiveSignWall (m : ℕ) (y : ℝ) : Prop :=
  IsLeast {x : ℝ | 0 < x ∧ signChangesAt (atomicFlag m) x} y

private def firstSignWallSequence (yFirst : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → firstPositiveSignWall m (yFirst m)

/-- Claim 18322: the first two cap cofactors have the stated ratio for the
one-atom denominator, whenever the rank and denominator are applicable. -/
def firstTwoCofactorRatio18322 : Prop :=
  ∀ (m : ℕ),
    1 ≤ m →
    capCofactor m 0 coshSqrtCoefficients ≠ 0 →
      capCofactor m 1 coshSqrtCoefficients /
          capCofactor m 0 coshSqrtCoefficients =
        -2 * (2 * (m : ℝ) - 1) * ((m : ℝ) + 1)

/-- Claim 18323: the first positive sign wall has the stated inverse-rank
scale, including the equivalent squared-parameter formulation. -/
def firstSignReversalScale18323 : Prop :=
  ∀ (yFirst : ℕ → ℝ),
    firstSignWallSequence yFirst →
      Tendsto
          (fun m : ℕ => (m : ℝ) * yFirst m)
          atTop (𝓝 (Real.pi / 4)) ∧
        Tendsto
          (fun m : ℕ => (m : ℝ) ^ 2 * (yFirst m) ^ 2)
          atTop (𝓝 (Real.pi ^ 2 / 16))

/-- Claim 18325: one fixed positive microscopic cap gives positive flags at
infinitely many ranks and negative flags at infinitely many ranks. -/
def fixedMicroscopicCapsReverseSignInfinitely18325 : Prop :=
  ∃ y : ℝ,
    0 < y ∧
      Set.Infinite {m : ℕ | atomicFlag m y > 0} ∧
      Set.Infinite {m : ℕ | atomicFlag m y < 0}

/-- Claim 18327: staying strictly before the first sign wall forces an
at-most inverse-rank cap scale, and no fixed positive cap stays before every
applicable rank. -/
def necessaryInverseRankCapScale18327 : Prop :=
  ∀ (yFirst : ℕ → ℝ),
    firstSignWallSequence yFirst →
      (∀ y₀ : ℝ,
        0 < y₀ →
        ¬(∀ m : ℕ, 1 ≤ m → y₀ < yFirst m)) ∧
      (∀ y : ℕ → ℝ,
        (∀ᶠ m : ℕ in atTop, 0 < y m ∧ y m < yFirst m) →
          ∃ C : ℝ,
            0 < C ∧
              ∀ᶠ m : ℕ in atTop, y m ≤ C / (m : ℝ))

end MathlibPlus.Open.Research.FormalizationR0151
