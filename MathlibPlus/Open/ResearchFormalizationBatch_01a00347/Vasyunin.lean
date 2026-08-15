import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Vasyunin

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The squarefree predicate used to define the Möbius coefficient. -/
def squarefreeNat (n : ℕ) : Prop :=
  0 < n ∧ ∀ q ∈ Nat.primeFactors n, ¬ q ^ 2 ∣ n

/-- The integer Möbius function, defined from prime-factor parity. -/
noncomputable def mobiusInteger (n : ℕ) : ℤ := by
  classical
  exact if squarefreeNat n then (-1 : ℤ) ^ (Nat.primeFactors n).card else 0

/-- The real Möbius coefficient used in the primitive-pair sums. -/
def mobiusReal (n : ℕ) : ℝ := (mobiusInteger n : ℝ)

/-- Euler's constant, by its convergent harmonic-logarithmic series. -/
def eulerMascheroni : ℝ :=
  ∑' n : ℕ,
    if n = 0 then 0
    else 1 / (n : ℝ) - Real.log (1 + 1 / (n : ℝ))

/-- Literal Vasyunin's finite cotangent row. -/
def vasyuninA (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n - 1),
    ((1 / 2 : ℝ) - Int.fract (((j * m : ℕ) : ℝ) / (n : ℝ))) *
      Real.cot (Real.pi * (j : ℝ) / (n : ℝ))

def cStar : ℝ :=
  eulerMascheroni - Real.log (2 * Real.pi)

/-- The exact Vasyunin kernel. -/
def psiEx (n m : ℕ) : ℝ :=
  Real.log (m : ℝ) - Real.log (n : ℝ) - cStar +
    Real.pi / (n : ℝ) * vasyuninA n m

/-- The exact primitive-pair kernel series. -/
def primitivePairKernelW (n m : ℕ) (x : ℝ) : ℝ :=
  ∑' d : ℕ,
    if 1 ≤ d ∧ Nat.Coprime d (n * m) ∧ 2 ≤ d * n ∧ 2 ≤ d * m then
      (mobiusReal d) ^ 2 / (d : ℝ) * x ^ (d * (n + m))
    else 0

/-- The literal row, kernel, and coprime-restricted series definitions. -/
def claim8445 : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → Nat.Coprime n m →
    vasyuninA n m =
      ∑ j ∈ Finset.Icc 1 (n - 1),
        ((1 / 2 : ℝ) - Int.fract (((j * m : ℕ) : ℝ) / (n : ℝ))) *
          Real.cot (Real.pi * (j : ℝ) / (n : ℝ)) ∧
    psiEx n m =
      Real.log (m : ℝ) - Real.log (n : ℝ) - cStar +
        Real.pi / (n : ℝ) * vasyuninA n m ∧
    ∀ x : ℝ, 0 < x → x < 1 →
      primitivePairKernelW n m x =
        ∑' d : ℕ,
          if 1 ≤ d ∧ Nat.Coprime d (n * m) ∧ 2 ≤ d * n ∧ 2 ≤ d * m then
            (mobiusReal d) ^ 2 / (d : ℝ) * x ^ (d * (n + m))
          else 0

/-- Bettin--Conrey's integral, represented as the literal complex Mellin integral. -/
def bettinConreyNu (h k : ℕ) : ℂ :=
  ((1 : ℂ) /
      ((2 * Real.pi * Real.sqrt (((h * k : ℕ) : ℝ))) : ℂ)) *
    ∫ t : ℝ,
      ((Complex.normSq
          (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) : ℂ) *
          Complex.exp
            ((t : ℂ) * Complex.I *
              Complex.log ((h : ℂ) / (k : ℂ))) /
        (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ))

/-- Bettin--Conrey symmetrization for the exact kernel. -/
def claim8446 : Prop :=
  ∀ h k : ℕ, 0 < h → 0 < k → Nat.Coprime h k →
    (((psiEx h k / (k : ℝ) + psiEx k h / (h : ℝ)) : ℝ) : ℂ) =
      (2 : ℂ) * bettinConreyNu h k

def mobiusMellinSeries (x t : ℝ) : ℂ :=
  ∑' a : ℕ,
    if 2 ≤ a then
      (mobiusInteger a : ℂ) * (x : ℂ) ^ a *
        Complex.exp
          (((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
            Complex.log (a : ℂ))
    else 0

def primitivePairBlock (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑' n : ℕ, ∑' m : ℕ,
      if 0 < n ∧ 0 < m ∧ Nat.Coprime n m then
        mobiusReal n * mobiusReal m *
          (psiEx n m / (m : ℝ) + psiEx m n / (n : ℝ)) *
            primitivePairKernelW n m x
      else 0

def primitivePairMellinRHS (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ t : ℝ,
      (Complex.normSq (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) /
          ((1 / 4 : ℝ) + t ^ 2)) *
        Complex.normSq (mobiusMellinSeries x t)

/-- The exact primitive-pair Mellin Gram identity. -/
def claim8447 : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 →
    primitivePairBlock x = primitivePairMellinRHS x

/-- Positivity of the exact primitive-pair block. -/
def claim8448 : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → 0 ≤ primitivePairBlock x

end

end MathlibPlus.Open.ResearchFormalization.Vasyunin
