import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

open scoped BigOperators

/-- The interval sum appearing in the coefficient polynomial. -/
noncomputable def intervalSum {t : ℕ} (i j : Fin t) : MvPolynomial (Fin t) ℤ :=
  Finset.sum (Finset.Icc i j) (fun k => MvPolynomial.X k)

/-- The polynomial f_t from claim R-3463. -/
noncomputable def f (t : ℕ) : MvPolynomial (Fin t) ℤ :=
  Finset.prod Finset.univ (fun i =>
    Finset.prod (Finset.Ioi i) (fun j =>
      (MvPolynomial.X j - MvPolynomial.X i))) *
    Finset.prod (Finset.univ.filter (fun i : Fin t => 1 ≤ i.1)) (fun i =>
      Finset.prod (Finset.Ioi i) (fun j => intervalSum i j))

/-- Total degree as the maximum total degree of a supported monomial. -/
def monomialDegree {t : ℕ} (d : Fin t →₀ ℕ) : ℕ :=
  d.sum (fun _ n => n)

def totalDegreeNat {t : ℕ} (P : MvPolynomial (Fin t) ℤ) : ℕ :=
  P.support.sup monomialDegree

/-- An ordering of a finite subset of a prime field. -/
def IsOrdering {p t : ℕ} (A : Finset (ZMod p)) (x : Fin t → ZMod p) : Prop :=
  Finset.univ.image x = A

/-- Pairwise distinct nonempty prefix partial sums of an ordering. -/
def PrefixPartialSumsDistinct {p t : ℕ} (x : Fin t → ZMod p) : Prop :=
  ∀ ⦃i j : Fin t⦄, i ≠ j →
    (Finset.sum (Finset.Iic i) x) ≠ Finset.sum (Finset.Iic j) x

/-- The coefficient criterion stated for the polynomial f_t. -/
noncomputable def intCoeff {t : ℕ} (d : Fin t →₀ ℕ) : ℤ :=
  MvPolynomial.coeff d (f t)

def CoefficientCriterion : Prop :=
  ∀ (t p : ℕ),
    1 ≤ t → Nat.Prime p →
    ∀ (A : Finset (ZMod p)),
      (∀ a ∈ A, a ≠ 0) → A.card = t →
      ∀ d : Fin t →₀ ℕ,
        (∀ i, d i ≤ t - 1) →
        monomialDegree d = (t - 1) ^ 2 →
        (intCoeff d : ZMod p) ≠ 0 →
        ∃ x : Fin t → ZMod p,
          IsOrdering A x ∧ PrefixPartialSumsDistinct x

/-- R-3463, claim 50883. -/
def claim50883 : Prop :=
  (∀ t : ℕ, 1 ≤ t → totalDegreeNat (f t) = (t - 1) ^ 2) ∧
    CoefficientCriterion

/-- The two explicit exponent vectors used by the rank-eight and rank-nine claims. -/
noncomputable def d8 : Fin 8 →₀ ℕ :=
  Finsupp.single 0 7 + Finsupp.single 1 5 + Finsupp.single 2 7 +
    Finsupp.single 3 7 + Finsupp.single 4 7 + Finsupp.single 5 7 +
    Finsupp.single 6 2 + Finsupp.single 7 7

noncomputable def d9 : Fin 9 →₀ ℕ :=
  Finsupp.single 0 8 + Finsupp.single 1 7 + Finsupp.single 2 6 +
    Finsupp.single 3 7 + Finsupp.single 4 7 + Finsupp.single 5 7 +
    Finsupp.single 6 7 + Finsupp.single 7 7 + Finsupp.single 8 8

/-- R-3463, claim 50888. -/
def claim50888 : Prop :=
  intCoeff d8 = 12 ∧
    (12 : ℤ) = 2 ^ 2 * 3 ∧
    (∀ (p : ℕ), Nat.Prime p → 8 < p →
      (intCoeff d8 : ZMod p) ≠ 0 ∧
        ∀ (A : Finset (ZMod p)),
          (∀ a ∈ A, a ≠ 0) → A.card = 8 →
          ∃ x : Fin 8 → ZMod p,
            IsOrdering A x ∧ PrefixPartialSumsDistinct x) ∧
    (∀ (p : ℕ), Nat.Prime p → p ≤ 8 →
      ¬ ∃ A : Finset (ZMod p),
        (∀ a ∈ A, a ≠ 0) ∧ A.card = 8)

/-- R-3463, claim 50889. -/
def claim50889 : Prop :=
  intCoeff d9 = -144324 ∧
    (144324 : ℤ) = 2 ^ 2 * 3 ^ 2 * 19 * 211 ∧
    (((intCoeff d9 : ℤ) : ZMod 19) = 0) ∧
    (((intCoeff d9 : ℤ) : ZMod 211) = 0) ∧
    ¬ (∀ (p : ℕ), Nat.Prime p → 9 < p →
      (intCoeff d9 : ZMod p) ≠ 0)

end ResearchFormalization
end Open
end MathlibPlus
