import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1578

open scoped BigOperators

noncomputable section

private abbrev F2Poly := Polynomial (ZMod 2)

private def sortedPositiveFour (A : Fin 4 → ℕ) : Prop :=
  (∀ i, 0 < A i) ∧
    ∀ i j, i ≤ j → A i ≤ A j

private def totalArmWeight (A : Fin 4 → ℕ) : ℕ :=
  ∑ i : Fin 4, A i

private def spiderArmPolynomial39338 (a : ℕ) : F2Poly :=
  ∑ k ∈ Finset.Icc 1 a,
    Polynomial.C ((a - k + 1 : ℕ) : ZMod 2) * Polynomial.X ^ k

private def spiderArmSeries39338 (a : ℕ) : F2Poly :=
  ∑ k ∈ Finset.range (a + 1), Polynomial.X ^ k

private def connectedSubtreeModTwo39338 (A : Fin 4 → ℕ) : F2Poly :=
  (∑ i : Fin 4, spiderArmPolynomial39338 (A i)) +
    Polynomial.X * ∏ i : Fin 4, spiderArmSeries39338 (A i)

private def affineK39338 (A : Fin 4 → ℕ) : F2Poly :=
  let b : Fin 4 → ℕ := fun i => A i + 1
  let S : F2Poly := ∑ i : Fin 4, Polynomial.X ^ b i
  let P : F2Poly := ∏ i : Fin 4, (1 + Polynomial.X ^ b i)
  P + (1 + Polynomial.X ^ 2) * S

/-- Claim 39338: sorted positive four-arm spiders of a common total are
rigid under connected-subtree congruence modulo two, equivalently under the
associated affine parity polynomial. -/
def claim39338_fourArmConnectedSubtreeModTwoRigidity : Prop :=
  ∀ A A' : Fin 4 → ℕ,
    sortedPositiveFour A →
      sortedPositiveFour A' →
        totalArmWeight A = totalArmWeight A' →
          ((connectedSubtreeModTwo39338 A = connectedSubtreeModTwo39338 A') ↔
            affineK39338 A = affineK39338 A') ∧
            (connectedSubtreeModTwo39338 A = connectedSubtreeModTwo39338 A' → A = A') ∧
              (affineK39338 A = affineK39338 A' → A = A')

end

end MathlibPlus.Open.ResearchFormalization.R1578
