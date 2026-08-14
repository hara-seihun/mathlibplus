import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.AdmittedBatch

noncomputable section

open scoped BigOperators
open MeasureTheory
open Set

/-- The primitive theta positive-shell moments appearing in Claim 56141. -/
def primitiveThetaMoment (j m : ℕ) : ℝ :=
  (2 : ℝ) / (Nat.factorial (2 * j) : ℝ) *
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (u / 2 - Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u)) *
        u ^ (2 * j)

/-- The hard-edge denominator in Claim 56141. -/
def primitiveThetaRho (m : ℕ) : ℝ :=
  2 * Real.pi * (m : ℝ) ^ 2 - (1 : ℝ) / 2

/-- The sum over all positive-shell indices at or beyond the cutoff. -/
def primitiveThetaTail (j M : ℕ) : ℝ :=
  ∑' m : ℕ, if M ≤ m then primitiveThetaMoment j m else 0

/--
Claim 56141: the primitive theta hard-edge estimate and the omitted-shell
Gaussian tail estimate.
-/
def primitive_theta_hard_edge_and_omitted_shell_tail : Prop :=
  (∀ (m j : ℕ), 1 ≤ m →
    0 ≤ primitiveThetaMoment j m ∧
      primitiveThetaMoment j m ≤
        (2 * Real.exp (-Real.pi * (m : ℝ) ^ 2)) /
          primitiveThetaRho m ^ (2 * j + 1)) ∧
  (∀ (M j : ℕ), 1 ≤ M →
    0 ≤ primitiveThetaTail j M ∧
      primitiveThetaTail j M ≤
        ((2 * Real.exp (-Real.pi * (M : ℝ) ^ 2)) /
            primitiveThetaRho M ^ (2 * j + 1)) *
          (1 + 1 / (2 * Real.pi * (M : ℝ))))

/-- Positive indices label the generators x_j with j ≥ 1. -/
abbrev PositiveIndex := {j : ℕ // 0 < j}

/-- The characteristic-zero component polynomial ring on x_j, j ≥ 1. -/
abbrev ComponentPolynomialRing := MvPolynomial PositiveIndex ℚ

/-- The generator x_j of the component polynomial ring. -/
def componentGenerator (j : ℕ) (hj : 0 < j) : ComponentPolynomialRing :=
  MvPolynomial.X ⟨j, hj⟩

/--
The coefficientwise linear operation Φ determined by
Φ(z^(q+1) f) = x_(q+1) f.  Its value on the constant coefficient is zero;
that value is irrelevant to the zP expressions in Claim 56179.
-/
def selectorPhi (P : Polynomial ComponentPolynomialRing) : ComponentPolynomialRing :=
  Finset.sum (Finset.range (P.natDegree + 1))
    (fun q => componentGenerator (Nat.succ q) (Nat.succ_pos q) * P.coeff (Nat.succ q))

/-- The intertwining identity used by the multiplicative selector claim. -/
def selectorIntertwining {A : Type*} [CommRing A] [Algebra ℚ A] [CharZero A]
    (η : ComponentPolynomialRing →ₐ[ℚ] A) (a b : A) : Prop :=
  ∀ P : Polynomial ComponentPolynomialRing,
    η (selectorPhi ((Polynomial.X : Polynomial ComponentPolynomialRing) * P)) =
      a * Polynomial.eval b (Polynomial.map η.toRingHom P)

/--
Claim 56179: over every commutative characteristic-zero ℚ-algebra, including
nonreduced algebras, the selector intertwining property is equivalent to the
geometric assignment η(x_j) = a b^(j-1) for every j ≥ 1.
-/
def multiplicative_selector_characters_exact : Prop :=
  ∀ (A : Type*) [CommRing A] [Algebra ℚ A] [CharZero A]
    (η : ComponentPolynomialRing →ₐ[ℚ] A) (a b : A),
    selectorIntertwining η a b ↔
      ∀ (j : ℕ) (hj : 0 < j),
        η (componentGenerator j hj) = a * b ^ (j - 1)

end

end MathlibPlus.Open.ResearchFormalization.AdmittedBatch
