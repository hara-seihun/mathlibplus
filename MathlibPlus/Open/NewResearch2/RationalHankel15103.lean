import Mathlib

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.RationalHankelStructure

noncomputable section

/-- Constant-term normalization of a nonzero polynomial, with the zero case
left explicit so the definition never invents a denominator. -/
def normalizeAtZero (F : Polynomial ℂ) : Polynomial ℂ :=
  if F.coeff 0 = 0 then F else (F.coeff 0)⁻¹ • F

/-- The common gcd of the denominator and all numerator components, with the
constant-one associate selected by the denominator convention. -/
def commonFroissartDivisor {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ) : Polynomial ℂ :=
  normalizeAtZero (Finset.fold gcd Q P Finset.univ)

/-- The reduced denominator `Q/G`. -/
def reducedDenominator {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ) : Polynomial ℂ :=
  Q / commonFroissartDivisor P Q

/-- The reduced numerator vector `P/G`. -/
def reducedNumerator {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ) : Fin d → Polynomial ℂ :=
  fun i => P i / commonFroissartDivisor P Q

/-- A normalized polynomial denominator representing the same vector rational
function as `P/Q`, expressed by cross multiplication in `ℂ[X]`. -/
def isCommonDenominator {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q D : Polynomial ℂ) : Prop :=
  D ≠ 0 ∧ D.coeff 0 = 1 ∧
    ∃ N : Fin d → Polynomial ℂ,
      ∀ i : Fin d, N i * Q = P i * D

/-- Maximality of the common removable divisor among constant-one divisors. -/
def isMaximalCommonDivisor {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q G : Polynomial ℂ) : Prop :=
  G ≠ 0 ∧ G.coeff 0 = 1 ∧
    G ∣ Q ∧ (∀ i : Fin d, G ∣ P i) ∧
    ∀ S : Polynomial ℂ,
      S ≠ 0 → S.coeff 0 = 1 → S ∣ Q →
        (∀ i : Fin d, S ∣ P i) → S ∣ G

/-- Minimality of a normalized common denominator under divisibility. -/
def isMinimalCommonDenominator {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q Qstar : Polynomial ℂ) : Prop :=
  isCommonDenominator P Q Qstar ∧
    ∀ D : Polynomial ℂ, isCommonDenominator P Q D → Qstar ∣ D

/-- Claim 15103: for a proper vector rational function with denominator
constant term one, the normalized common gcd is the exact Froissart divisor,
and division by it produces the minimal normalized common denominator and
unchanged represented vector rational function. -/
def claim_15103 : Prop :=
  ∀ d : ℕ, ∀ P : Fin d → Polynomial ℂ, ∀ Q : Polynomial ℂ,
    Q ≠ 0 → Q.coeff 0 = 1 →
      (∀ i : Fin d, (P i).degree < Q.degree) →
      let G := commonFroissartDivisor P Q
      let Qstar := reducedDenominator P Q
      let Pstar := reducedNumerator P Q
      isMaximalCommonDivisor P Q G ∧
        Q = G * Qstar ∧
        (∀ i : Fin d, P i = G * Pstar i) ∧
        isMinimalCommonDenominator P Q Qstar ∧
        (∀ i : Fin d, Pstar i * Q = P i * Qstar)

end
end MathlibPlus.Open.NewResearch2.RationalHankelStructure
