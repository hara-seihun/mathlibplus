import Mathlib
import MathlibPlus.Algebra.Claim29919

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1061.Claim29924

noncomputable section

open Polynomial

def denominatorPolynomial (p q : ℕ) (δ : ℚ) : Polynomial ℚ :=
  Polynomial.C (δ * ((q : ℚ) - (p : ℚ))) +
    Polynomial.C ((q : ℚ) * ((p : ℚ) - δ)) * Polynomial.X ^ p +
    Polynomial.C ((p : ℚ) * (δ - (q : ℚ))) * Polynomial.X ^ q

def elementarySymmetricStatistic {q : ℕ}
    (roots : Fin q → ℚ) (k : ℕ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset (Fin q)).powersetCard k,
    S.prod roots

def cavityCharacteristicPolynomial {q : ℕ}
    (roots : Fin q → ℚ) : Polynomial ℚ :=
  ∏ i : Fin q, (Polynomial.X - Polynomial.C (roots i))

structure PositiveRootPacket (p q : ℕ) (δ : ℚ) where
  leadingCoeff : ℚ
  roots : Fin q → ℚ
  leadingCoeff_ne_zero : leadingCoeff ≠ 0
  roots_nonnegative : ∀ i, 0 ≤ roots i
  roots_ne_zero : ∀ i, roots i ≠ 0
  base_root : ∃ i, roots i = 1
  factorization :
    denominatorPolynomial p q δ =
      Polynomial.C leadingCoeff * cavityCharacteristicPolynomial roots

def claim29924_vietaObstructionConsecutiveExponents : Prop :=
  ∀ {p q : ℕ} {δ : ℚ},
    0 < p →
      p < q →
        q = p + 1 →
          3 ≤ q →
            δ ≠ 0 →
              δ ≠ (p : ℚ) →
                δ ≠ (q : ℚ) →
                  ∀ packet : PositiveRootPacket p q δ,
                    (denominatorPolynomial p q δ).coeff (q - 2) = 0 ∧
                      elementarySymmetricStatistic packet.roots 2 = 0 ∧
                        ¬ (∀ i, 0 < packet.roots i)

end

end MathlibPlus.Open.ResearchFormalization.R1061.Claim29924
