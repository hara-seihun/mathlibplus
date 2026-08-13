import Mathlib

noncomputable section

namespace MathlibPlus.Open.Algebraic.ReciprocalBatch

open scoped BigOperators
open Polynomial

private def sourcePolynomial : Polynomial ℚ :=
  X ^ 6 + 2 * X ^ 4 + X ^ 3 + 2 * X ^ 2 + 1

private def sourcePolynomialC : Polynomial ℂ :=
  sourcePolynomial.map (algebraMap ℚ ℂ)

private def exteriorRoots : Multiset ℂ :=
  sourcePolynomialC.roots.filter (fun z => (1 : ℝ) < ‖z‖)

private def unitRoots : Multiset ℂ :=
  sourcePolynomialC.roots.filter (fun z => ‖z‖ = (1 : ℝ))

private def beta : ℝ :=
  (Multiset.prod exteriorRoots).re

private def betaMinpoly : Polynomial ℚ :=
  minpoly ℚ beta

private def betaConjugateModuli : Multiset ℝ :=
  (betaMinpoly.map (algebraMap ℚ ℂ)).roots.map (fun z => ‖z‖)

private def polynomialMahler (p : Polynomial ℚ) : ℝ :=
  Multiset.prod ((p.map (algebraMap ℚ ℂ)).roots.map (fun z => max ‖z‖ 1))

private def algebraicMahler (x : ℝ) : ℝ :=
  Multiset.prod (((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots.map
    (fun z => max ‖z‖ 1))

private def algebraicUnit (x : ℝ) : Prop :=
  IsIntegral ℤ x ∧ IsIntegral ℤ x⁻¹

private def perronNumber (x : ℝ) : Prop :=
  1 < x ∧ IsIntegral ℤ x ∧
    (∀ z : ℂ, z ∈ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots → ‖z‖ ≤ x) ∧
    ∃! z : ℂ,
      z ∈ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots ∧ ‖z‖ = x

private def pisotNumber (x : ℝ) : Prop :=
  1 < x ∧ IsIntegral ℤ x ∧
    (x : ℂ) ∈ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots ∧
    ∀ z : ℂ,
      z ∈ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots →
        z = (x : ℂ) ∨ ‖z‖ < 1

private def salemNumber (x : ℝ) : Prop :=
  1 < x ∧ IsIntegral ℤ x ∧ 4 ≤ (minpoly ℚ x).natDegree ∧
    (x : ℂ) ∈ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots ∧
    ((x⁻¹ : ℝ) : ℂ) ∈ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots ∧
    ∀ z : ℂ,
      z ∈ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots →
        z = (x : ℂ) ∨ z = ((x⁻¹ : ℝ) : ℂ) ∨ ‖z‖ = 1

/-- Exact reciprocal, irreducibility, noncyclotomicity, and root-count claim. -/
def claim13257 : Prop :=
  sourcePolynomial.Monic ∧
    sourcePolynomial.reverse = sourcePolynomial ∧
    Irreducible sourcePolynomial ∧
    sourcePolynomial.natDegree = 6 ∧
    (∀ z : ℂ, sourcePolynomialC.IsRoot z →
      ∀ n : ℕ, z ^ (n + 1) ≠ 1) ∧
    exteriorRoots.card = 2 ∧
    unitRoots.card = 2 ∧
    ∃ z : ℂ,
      sourcePolynomialC.IsRoot z ∧
        sourcePolynomialC.IsRoot z⁻¹ ∧ ‖z‖ = (1 : ℝ)

/-- The exterior-root product, its degree, and its complete conjugate-modulus ledger. -/
def claim13258 : Prop :=
  ∃ a : ℝ,
    1 < beta ∧ 1 < a ∧
      (Multiset.prod exteriorRoots : ℂ) = (beta : ℂ) ∧
      polynomialMahler sourcePolynomial = beta ∧
      beta = a ^ 2 ∧
      Irreducible (minpoly ℚ beta) ∧
      (minpoly ℚ beta).natDegree = 12 ∧
      betaConjugateModuli =
        (Multiset.ofList [a ^ 2, a, a, a, a, 1, 1, a⁻¹, a⁻¹, a⁻¹, a⁻¹, a⁻¹ ^ 2] : Multiset ℝ)

/-- The exponent ledger gives a Perron algebraic unit but neither a Pisot nor Salem number. -/
def claim13259 : Prop :=
  ∃ a : ℝ,
    1 < a ∧ beta = a ^ 2 ∧
      perronNumber beta ∧ algebraicUnit beta ∧
      betaConjugateModuli =
        (Multiset.ofList [a ^ 2, a, a, a, a, 1, 1, a⁻¹, a⁻¹, a⁻¹, a⁻¹, a⁻¹ ^ 2] : Multiset ℝ) ∧
      ¬ pisotNumber beta ∧ ¬ salemNumber beta

/-- Every positive power generates the same field as the exterior-root product. -/
def claim13261 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    Algebra.adjoin ℚ ({beta ^ m} : Set ℝ) = Algebra.adjoin ℚ ({beta} : Set ℝ)

/-- Positive powers preserve the algebraic degree, here exactly twelve. -/
def claim13262 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (minpoly ℚ (beta ^ m)).natDegree = (minpoly ℚ beta).natDegree ∧
      (minpoly ℚ (beta ^ m)).natDegree = 12

/-- Mahler measure scales multiplicatively on every positive power. -/
def claim13263 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    algebraicMahler (beta ^ m) = algebraicMahler beta ^ m ∧
      algebraicMahler (beta ^ m) = beta ^ (3 * m)

end MathlibPlus.Open.Algebraic.ReciprocalBatch
