import MathlibPlus.Open.NewResearch2.RationalHankel15103

open scoped BigOperators
open Polynomial
open Classical

namespace MathlibPlus.Open.NewResearch2.RationalHankelStructure

noncomputable section

/-- The coefficient of the vector Taylor series represented by `Pstar/Qstar`.
The denominator has constant term one in the admitted rational-function setting,
so this is the coefficient of `Pstar * Qstar⁻¹` in formal power series. -/
def vectorTaylorCoeff {d : ℕ} (Pstar : Fin d → Polynomial ℂ)
    (Qstar : Polynomial ℂ) (n : ℕ) (i : Fin d) : ℂ :=
  PowerSeries.coeff n
    ((Pstar i : PowerSeries ℂ) * (Qstar : PowerSeries ℂ)⁻¹)

/-- The block Hankel carrier with `L` vector-channel blocks and `K` columns. -/
def blockHankel {d L K : ℕ} (c : ℕ → Fin d → ℂ) (ν : ℕ) :
    Matrix (Fin L × Fin d) (Fin K) ℂ :=
  fun ij k => c (ij.1.val + k.val + ν) ij.2

/-- The polynomial interpretation of `x^r Q(x⁻¹)`. -/
def reciprocalPolynomial (Q : Polynomial ℂ) : Polynomial ℂ :=
  Q.reverse

/-- No non-unit polynomial is common to all numerator components and the
reduced denominator. -/
def hasNoCommonFactor {d : ℕ} (Pstar : Fin d → Polynomial ℂ)
    (Qstar : Polynomial ℂ) : Prop :=
  ∀ D : Polynomial ℂ,
    D ∣ Qstar → (∀ i : Fin d, D ∣ Pstar i) → IsUnit D

/-- Every pole node has a nonzero highest vector residue jet. -/
def highestVectorResidueJetNonzero {d J : ℕ}
    (m : Fin J → ℕ) (b : ∀ j : Fin J, Fin (m j) → Fin d → ℂ) : Prop :=
  ∀ j : Fin J,
    ∃ s : Fin (m j), s.val + 1 = m j ∧ ∃ i : Fin d, b j s i ≠ 0

/-- A matrix has a cyclic vector when its first `r` iterates form a basis. -/
def cyclicMatrix {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ b : Fin r → ℂ,
    Function.Bijective (fun a : Fin r → ℂ =>
      ∑ k : Fin r, a k • (A ^ k.val).mulVec b)

/-- A single Jordan chain of length `m j` is supplied at each node `lam j`,
with the chains together forming a basis. -/
def jordanChains {J r : ℕ} (m : Fin J → ℕ) (lam : Fin J → ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ basis : (Σ j : Fin J, Fin (m j)) → (Fin r → ℂ),
    Function.Bijective (fun a : (Σ j : Fin J, Fin (m j)) → ℂ =>
      ∑ q, a q • basis q) ∧
    ∀ (j : Fin J) (s : Fin (m j)),
      A.mulVec (basis ⟨j, s⟩) =
        lam j • basis ⟨j, s⟩ +
          (if h : s.val + 1 < m j then
            basis ⟨j, ⟨s.val + 1, h⟩⟩
           else 0)

/-- Claim 15104: the reciprocal of the exact minimal denominator is the
recurrence polynomial of the vector Taylor coefficients, including the
constant-degree case. -/
def claim_15104 : Prop :=
  ∀ d : ℕ, ∀ P : Fin d → Polynomial ℂ, ∀ Q : Polynomial ℂ,
    Q ≠ 0 → Q.coeff 0 = 1 →
      (∀ i : Fin d, (P i).degree < Q.degree) →
      let Qstar := reducedDenominator P Q
      let Pstar := reducedNumerator P Q
      let r := Qstar.natDegree
      ∀ q : Fin r → ℂ,
        Qstar = (1 : Polynomial ℂ) +
            ∑ k : Fin r, Polynomial.C (q k) * Polynomial.X ^ (k.val + 1) →
          reciprocalPolynomial Qstar =
              Polynomial.X ^ r +
                ∑ k : Fin r,
                  Polynomial.C (q k) * Polynomial.X ^ (r - (k.val + 1)) ∧
            ∀ n : ℕ, ∀ i : Fin d,
              vectorTaylorCoeff Pstar Qstar (n + r) i +
                  ∑ k : Fin r,
                    q k * vectorTaylorCoeff Pstar Qstar
                      (n + r - (k.val + 1)) i = 0

/-- Claim 15105: after the exact denominator is factored at distinct pole
nodes, the represented vector Taylor coefficients have a confluent
exponential-polynomial expansion.  The residue coefficients are witnesses
for that represented sequence, not unconstrained universally quantified data;
their highest vector jets express the minimal-denominator/no-common-factor
condition. -/
def claim_15105 : Prop :=
  ∀ d : ℕ, ∀ P : Fin d → Polynomial ℂ, ∀ Q : Polynomial ℂ,
    Q ≠ 0 → Q.coeff 0 = 1 →
      (∀ i : Fin d, (P i).degree < Q.degree) →
      let Qstar := reducedDenominator P Q
      let Pstar := reducedNumerator P Q
      let r := Qstar.natDegree
      ∀ J : ℕ, ∀ m : Fin J → ℕ, ∀ lam : Fin J → ℂ,
        (∀ j : Fin J, 0 < m j) →
        (∀ ⦃j k : Fin J⦄, j ≠ k → lam j ≠ lam k) →
        (∑ j : Fin J, m j) = r →
        Qstar =
          ∏ j : Fin J,
            ((1 : Polynomial ℂ) - Polynomial.C (lam j) * Polynomial.X) ^ m j →
        ∃ b : ∀ j : Fin J, Fin (m j) → Fin d → ℂ,
          (∀ n : ℕ, ∀ i : Fin d,
            vectorTaylorCoeff Pstar Qstar n i =
              ∑ j : Fin J, ∑ s : Fin (m j),
                b j s i * (Nat.choose n s.val : ℂ) * lam j ^ (n - s.val)) ∧
          highestVectorResidueJetNonzero m b ∧
          (highestVectorResidueJetNonzero m b ↔
            (hasNoCommonFactor Pstar Qstar ∧
              isMinimalCommonDenominator P Q Qstar))

/-- Claim 15106: the exact vector block Hankel matrices of the represented
sequence have rank `r` at shift zero and contain an invertible `r` by `r`
row/column pivot when both block lengths reach the minimal order. -/
def claim_15106 : Prop :=
  ∀ d : ℕ, ∀ P : Fin d → Polynomial ℂ, ∀ Q : Polynomial ℂ,
    Q ≠ 0 → Q.coeff 0 = 1 →
      (∀ i : Fin d, (P i).degree < Q.degree) →
      let Qstar := reducedDenominator P Q
      let Pstar := reducedNumerator P Q
      let r := Qstar.natDegree
      ∀ L K : ℕ, r ≤ L → r ≤ K →
        let c : ℕ → Fin d → ℂ := vectorTaylorCoeff Pstar Qstar
        let H₀ := blockHankel c 0
        Matrix.rank H₀ = r ∧
          ∃ I : Fin r → (Fin L × Fin d),
            ∃ J : Fin r → Fin K,
              Function.Injective I ∧ Function.Injective J ∧
                Matrix.det (H₀.submatrix I J) ≠ 0

/-- Claim 15107: for every invertible matching pivot of the exact Hankel pair,
the shifted pivot is the conjugate of a cyclic realization whose determinant
polynomial is the exact denominator and whose Jordan chains are the reciprocal
pole nodes with their confluent multiplicities. -/
def claim_15107 : Prop :=
  ∀ d : ℕ, ∀ P : Fin d → Polynomial ℂ, ∀ Q : Polynomial ℂ,
    Q ≠ 0 → Q.coeff 0 = 1 →
      (∀ i : Fin d, (P i).degree < Q.degree) →
      let Qstar := reducedDenominator P Q
      let Pstar := reducedNumerator P Q
      let r := Qstar.natDegree
      ∀ J : ℕ, ∀ m : Fin J → ℕ, ∀ lam : Fin J → ℂ,
        (∀ j : Fin J, 0 < m j) →
        (∀ ⦃j k : Fin J⦄, j ≠ k → lam j ≠ lam k) →
        (∑ j : Fin J, m j) = r →
        Qstar =
          ∏ j : Fin J,
            ((1 : Polynomial ℂ) - Polynomial.C (lam j) * Polynomial.X) ^ m j →
        ∀ L K : ℕ, r ≤ L → r ≤ K →
          let c : ℕ → Fin d → ℂ := vectorTaylorCoeff Pstar Qstar
          let H₀ := blockHankel c 0
          let H₁ := blockHankel c 1
          ∀ I : Fin r → (Fin L × Fin d),
            ∀ Jidx : Fin r → Fin K,
              Function.Injective I → Function.Injective Jidx →
                Matrix.det (H₀.submatrix I Jidx) ≠ 0 →
                let G₀ := H₀.submatrix I Jidx
                let G₁ := H₁.submatrix I Jidx
                ∃ A X Xinv : Matrix (Fin r) (Fin r) ℂ,
                  X * Xinv = 1 ∧ Xinv * X = 1 ∧
                  G₁ * G₀⁻¹ = X * A * Xinv ∧
                  cyclicMatrix A ∧
                  Matrix.det
                      (fun i j =>
                        (if i = j then (1 : Polynomial ℂ) else 0) -
                          Polynomial.C (A i j) * Polynomial.X) = Qstar ∧
                  jordanChains m lam A

end
end MathlibPlus.Open.NewResearch2.RationalHankelStructure
