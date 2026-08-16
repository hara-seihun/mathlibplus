import Mathlib

namespace MathlibPlus.Open.Combinatorics.FormalizationBatch

open scoped BigOperators
noncomputable section

def rankFourPolynomial (ε : ℝ) : ℝ :=
  2097152 * ε ^ 7
    + 55500425216 * ε ^ 6
    - 17984666444304 * ε ^ 5
    + 54202816766341 * ε ^ 4
    - 1270038175574324 * ε ^ 3
    + 1555972249399296 * ε ^ 2
    - 9009293588168704 * ε
    + 9007199254740992

def rankFourMoment (ε : ℝ) (j : ℕ) : ℝ :=
  1 + ε * ((4 : ℝ)⁻¹) ^ j

def rankFourFactorialMoment (ε : ℝ) (j : ℕ) : ℝ :=
  rankFourMoment ε j / (Nat.factorial (2 * j) : ℝ)

def rankFourCompletedBezout (ε : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    Finset.sum (Finset.range (min i.val j.val + 1)) (fun a =>
      ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ)
        * rankFourFactorialMoment ε a
        * rankFourFactorialMoment ε (i.val + j.val + 1 - a))

def rankFourDeterminant (ε : ℝ) : ℝ :=
  Matrix.det (rankFourCompletedBezout ε)

def rankFourSimpleCrossing (P : ℝ → ℝ) (r : ℝ) : Prop :=
  P r = 0 ∧
    deriv P r ≠ 0 ∧
    ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ < η → P (r - δ) * P (r + δ) < 0

def rankFourNegativeInterval_claim12545 : Prop :=
  ∃ r₁ r₂ : ℝ,
    0 < r₁ ∧
    r₁ < r₂ ∧
    rankFourPolynomial 0 > 0 ∧
    rankFourSimpleCrossing rankFourPolynomial r₁ ∧
    rankFourSimpleCrossing rankFourPolynomial r₂ ∧
    (∀ x : ℝ,
      0 < x → rankFourPolynomial x = 0 → x = r₁ ∨ x = r₂) ∧
    (∀ ε : ℝ,
      rankFourDeterminant ε =
        ((ε + 1) * rankFourPolynomial ε) /
          (903931901687350576475327692800000 : ℝ)) ∧
    ∀ ε : ℝ, r₁ < ε → ε < r₂ → rankFourDeterminant ε < 0

end
end MathlibPlus.Open.Combinatorics.FormalizationBatch
