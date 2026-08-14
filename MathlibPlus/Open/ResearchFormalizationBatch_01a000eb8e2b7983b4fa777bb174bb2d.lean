import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000eb8e2b7983b4fa777bb174bb2d

open Polynomial

noncomputable section

/-- Polynomial notation used by the long-end formulas in the packet. -/
def spiderL : Polynomial ℤ := 1 + X

def spiderQ : Polynomial ℤ := X ^ 2 + X + 1

def spiderD (a b : ℕ) : ℕ := a + b

def spiderN (a b : ℕ) : ℕ := 1 + a + 2 * b

def spiderH (a b : ℕ) : Polynomial ℤ :=
  spiderL ^ a * spiderQ ^ (b - 1)

def longEndB (a b : ℕ) : Polynomial ℤ :=
  spiderH a b + X ^ (spiderN a b - 2) * spiderQ

def longEndA (a b : ℕ) : Polynomial ℤ :=
  (spiderQ + spiderL + 1) * spiderH a b -
    X ^ (spiderN a b - 4) *
      (X ^ 3 + C (Int.ofNat (spiderD a b + 1)) * X ^ 2 +
        C (Int.ofNat (spiderD a b + 1)) * X +
        C (Int.ofNat (spiderD a b - 1)))

def gInt (d : ℕ) : Polynomial ℤ :=
  X ^ 6 + C 3 * X ^ 5 + C 6 * X ^ 4 + C 6 * X ^ 3 +
    C (Int.ofNat (d + 4)) * X ^ 2 +
    C (Int.ofNat (d + 1)) * X + C (Int.ofNat d) - C 1

def gRat (d : ℕ) : Polynomial ℚ :=
  X ^ 6 + C 3 * X ^ 5 + C 6 * X ^ 4 + C 6 * X ^ 3 +
    C (d + 4 : ℚ) * X ^ 2 + C (d + 1 : ℚ) * X + C (d : ℚ) - C 1

def gMod2 (d : ℕ) : Polynomial (ZMod 2) :=
  X ^ 6 + C 3 * X ^ 5 + C 6 * X ^ 4 + C 6 * X ^ 3 +
    C (d + 4 : ZMod 2) * X ^ 2 + C (d + 1 : ZMod 2) * X + C (d : ZMod 2) - C 1

def complexEval (x : ℂ) (p : Polynomial ℤ) : ℂ :=
  eval₂ (Int.castRingHom ℂ) x p

def claim30622 : Prop :=
  ∀ (a b : ℕ), 0 < b → 2 ≤ spiderD a b →
    ∀ x : ℂ,
      complexEval x (longEndA a b) = 0 →
        complexEval x (longEndB a b) = 0 →
          eval₂ (Int.castRingHom ℂ) x (gInt (spiderD a b)) = 0

def claim30623 : Prop :=
  (∀ d : ℕ, Even d →
    gMod2 d =
        (X + 1) ^ 2 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ∧
      Irreducible (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : Polynomial (ZMod 2))) ∧
    (∀ d : ℕ, Odd d →
      gMod2 d = X ^ 2 * (X ^ 4 + X ^ 3 + 1) ∧
        Irreducible (X ^ 4 + X ^ 3 + 1 : Polynomial (ZMod 2)))

def claim30624 : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ p r : Polynomial ℚ,
      gRat d = p * r →
        0 < p.natDegree → 0 < r.natDegree →
          p.natDegree = 1 ∨ p.natDegree = 2 ∨
            r.natDegree = 1 ∨ r.natDegree = 2

def polynomialCoprime (p q : Polynomial ℤ) : Prop :=
  ∀ r : Polynomial ℤ, r ∣ p → r ∣ q → r.natDegree = 0

def claim30631 : Prop :=
  (∀ (a b : ℕ), 0 < b → spiderD a b = 2 →
    (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 2)) ∧
    Polynomial.resultant (longEndA 1 1) (longEndB 1 1) = 16 ∧
    Polynomial.resultant (longEndA 0 2) (longEndB 0 2) = 98 ∧
    Polynomial.resultant (longEndA 1 1) (longEndB 1 1) ≠ 0 ∧
    Polynomial.resultant (longEndA 0 2) (longEndB 0 2) ≠ 0 ∧
    polynomialCoprime (longEndA 1 1) (longEndB 1 1) ∧
    polynomialCoprime (longEndA 0 2) (longEndB 0 2)

def claim30633 : Prop :=
  ∀ (a₁ b₁ a₂ b₂ : ℕ), 0 < b₁ → 0 < b₂ →
    longEndB a₁ b₁ = longEndB a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a000eb8e2b7983b4fa777bb174bb2d
