import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch.Polynomial

abbrev Exp7 := Fin 7 →₀ ℕ

noncomputable def expVec (v : Fin 7 → ℕ) : Exp7 :=
  Finsupp.equivFunOnFinite.symm v

noncomputable def monomialSymmetric (v : Fin 7 → ℕ) : MvPolynomial (Fin 7) ℤ :=
  ∑ e ∈ (Finset.univ.image (fun σ : Equiv.Perm (Fin 7) =>
    expVec (fun i => v (σ i)))),
    MvPolynomial.monomial e 1

def p7 : Fin 7 → ℕ := ![7, 0, 0, 0, 0, 0, 0]
def p52 : Fin 7 → ℕ := ![5, 2, 0, 0, 0, 0, 0]
def p511 : Fin 7 → ℕ := ![5, 1, 1, 0, 0, 0, 0]
def p43 : Fin 7 → ℕ := ![4, 3, 0, 0, 0, 0, 0]
def p421 : Fin 7 → ℕ := ![4, 2, 1, 0, 0, 0, 0]
def p4111 : Fin 7 → ℕ := ![4, 1, 1, 1, 0, 0, 0]
def p331 : Fin 7 → ℕ := ![3, 3, 1, 0, 0, 0, 0]
def p322 : Fin 7 → ℕ := ![3, 2, 2, 0, 0, 0, 0]
def p3211 : Fin 7 → ℕ := ![3, 2, 1, 1, 0, 0, 0]
def p31111 : Fin 7 → ℕ := ![3, 1, 1, 1, 1, 0, 0]
def p2221 : Fin 7 → ℕ := ![2, 2, 2, 1, 0, 0, 0]
def p22111 : Fin 7 → ℕ := ![2, 2, 1, 1, 1, 0, 0]
def p211111 : Fin 7 → ℕ := ![2, 1, 1, 1, 1, 1, 0]
def p1111111 : Fin 7 → ℕ := ![1, 1, 1, 1, 1, 1, 1]

noncomputable def R : MvPolynomial (Fin 7) ℤ :=
    10800 * monomialSymmetric p7
  - 4200 * monomialSymmetric p52
  + 4200 * monomialSymmetric p511
  - 5600 * monomialSymmetric p43
  + 5040 * monomialSymmetric p421
  - 3360 * monomialSymmetric p4111
  + 5110 * monomialSymmetric p331
  + 7896 * monomialSymmetric p322
  - 5208 * monomialSymmetric p3211
  + 13146 * monomialSymmetric p31111
  - 7560 * monomialSymmetric p2221
  + 16352 * monomialSymmetric p22111
  - 56840 * monomialSymmetric p211111
  + 524895 * monomialSymmetric p1111111

noncomputable def orderedSubstitution (i : Fin 7) : MvPolynomial (Fin 7) ℤ :=
  ∑ j ∈ Finset.Icc i (6 : Fin 7), MvPolynomial.X j

noncomputable def orderedR : MvPolynomial (Fin 7) ℤ :=
  MvPolynomial.eval₂
    (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 7) ℤ)
    orderedSubstitution R

noncomputable def RReal : MvPolynomial (Fin 7) ℝ :=
  MvPolynomial.map (Int.castRingHom ℝ) R

noncomputable def degreeSevenExponents : Finset Exp7 :=
  (Finset.univ.filter (fun v : Fin 7 → Fin 8 =>
    (∑ i : Fin 7, (v i).val) = 7)).image
    (fun v => expVec (fun i => (v i).val))

noncomputable def y7Exponent : Exp7 :=
  expVec ![0, 0, 0, 0, 0, 0, 7]

/-- Claim 966: the ordered-chamber expansion has exactly the asserted positive coefficients. -/
def claim966 : Prop :=
  degreeSevenExponents.card = Nat.choose 13 6 ∧
    (∀ d : Exp7, d ∈ degreeSevenExponents →
      0 < MvPolynomial.coeff d orderedR) ∧
    (∀ d : Exp7, d ∈ degreeSevenExponents →
      (2000 : ℤ) ≤ MvPolynomial.coeff d orderedR ∧
      MvPolynomial.coeff d orderedR ≤ 405003375) ∧
    (∃ d : Exp7, d ∈ degreeSevenExponents ∧
      MvPolynomial.coeff d orderedR = 2000) ∧
    (∃ d : Exp7, d ∈ degreeSevenExponents ∧
      MvPolynomial.coeff d orderedR = 405003375) ∧
    (∑ d ∈ degreeSevenExponents, MvPolynomial.coeff d orderedR =
      59408039040) ∧
    MvPolynomial.coeff y7Exponent orderedR = 1764735 ∧
    (∀ β : Fin 7 → ℝ,
      (∀ i j : Fin 7, i ≤ j → β j ≤ β i) →
      (∀ i : Fin 7, 0 < β i) →
      0 < MvPolynomial.eval (fun i => β i) RReal)

end MathlibPlus.Open.ResearchFormalization.Batch.Polynomial
