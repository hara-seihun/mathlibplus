import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.NewResearch2.R0578

private def wordCapacityCondition (w : ℕ → ℕ) : Prop :=
  (∀ n, n < 4 → w n = 0) ∧
    w 4 = 1 ∧ w 5 = 2 ∧
      ∀ n, 4 ≤ n → w (n + 2) = 2 * w (n + 1) + 3 * w n

private def oddProduct (r : ℕ) : ℚ :=
  Finset.prod (Finset.range r) (fun i => ((2 * i + 1 : ℕ) : ℚ))

private abbrev corePolynomialRing := MvPolynomial (Fin 3 ⊕ Fin 3) ℚ

private def coreX (i : Fin 3) : corePolynomialRing :=
  MvPolynomial.X (Sum.inl i)

private def coreY (i : Fin 3) : corePolynomialRing :=
  MvPolynomial.X (Sum.inr i)

private def coreCoordinate (i : Fin 6) : corePolynomialRing :=
  match i.val with
  | 0 => coreX 0
  | 1 => coreX 1
  | 2 => coreX 2
  | 3 => coreY 0
  | 4 => coreY 1
  | _ => coreY 2

private def fixedCoreIdeal : Ideal corePolynomialRing :=
  Ideal.span ({
    (6 : corePolynomialRing) * coreX 1,
    (2 : corePolynomialRing) * (coreX 0 + coreX 2),
    (12 : corePolynomialRing) * (coreX 1 ^ 2),
    (2 : corePolynomialRing) * (coreY 0 + coreY 2 + coreX 0 * coreX 2),
    coreX 0 ^ 2 + coreX 2 ^ 2 +
      2 * (coreX 0 * coreX 1 + coreX 1 * coreX 2 + coreY 1)
  } : Set corePolynomialRing)

private def coordinateVector (a : Fin 6 → ℚ) : Fin 6 → ℚ := a

private def rowVector (j : Fin 5) : Fin 6 → ℚ :=
  match j.val with
  | 0 => fun i => if i = 0 then 1 else 0
  | 1 => fun i => if i = 1 then 1 else 0
  | 2 => fun i => if i = 2 then 1 else if i = 3 then 2 else 0
  | 3 => fun i => if i = 3 then 2 else if i = 5 then 2 else 0
  | _ => fun i => if i = 1 then 2 else if i = 2 then 1 else if i = 4 then 2 else 0

/-- Claim 22907: the weighted word capacity has the stated recurrence and
characteristic roots. -/
def weighted_word_capacity_recurrence_claim22907 : Prop :=
  (∃! w : ℕ → ℕ, wordCapacityCondition w) ∧
    (∀ r : ℝ, r ^ 2 = 2 * r + 3 → r = 3 ∨ r = -1) ∧
    (3 : ℝ) > |(-1 : ℝ)|

/-- Claim 22913: the fixed-core ideal quotient is the polynomial algebra on
`x₀,y₀`, with the four displayed eliminated variables. -/
def fixed_core_source_ideal_claim22913 : Prop :=
  let R := corePolynomialRing
  let J := fixedCoreIdeal
  ¬ FiniteDimensional ℚ (R ⧸ J) ∧
    (∃ e : (R ⧸ J) ≃ₐ[ℚ] MvPolynomial (Fin 2) ℚ,
    e (Ideal.Quotient.mk J (coreX 0)) = MvPolynomial.X 0 ∧
      e (Ideal.Quotient.mk J (coreY 0)) = MvPolynomial.X 1 ∧
      e (Ideal.Quotient.mk J (coreX 1)) = 0 ∧
      e (Ideal.Quotient.mk J (coreX 2)) = -MvPolynomial.X 0 ∧
      e (Ideal.Quotient.mk J (coreY 1)) = -(MvPolynomial.X 0 ^ 2) ∧
      e (Ideal.Quotient.mk J (coreY 2)) =
        MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1)

/-- Claim 22914: the reversal-invariant degree-two span has rank five and its
one-dimensional cokernel is detected by the stated coordinate functional. -/
def reversal_invariant_degree_two_cokernel_claim22914 : Prop :=
  let M : Matrix (Fin 6) (Fin 5) ℚ := fun i j => rowVector j i
  let ell : (Fin 6 → ℚ) → ℚ :=
    fun v => -2 * v 2 + v 3 + v 4 - v 5
  Matrix.rank M = 5 ∧
    (∀ j : Fin 5, ell (rowVector j) = 0) ∧
    ∃ v : Fin 6 → ℚ, ell v ≠ 0

end MathlibPlus.Open.NewResearch2.R0578
