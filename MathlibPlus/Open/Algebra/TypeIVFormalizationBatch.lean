import Mathlib

namespace MathlibPlus.Open.Algebra

open scoped Polynomial

/-- Claim 9292: explicit integral polynomial data for a type-IV witness. -/
def claim9292_typeIVDatum (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]) : Prop :=
  ell.Monic ∧ A.Monic ∧ A.natDegree = 2 * n + 1 ∧
    (∀ z : ℂ, z ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ℂ) z R =
            z ^ n * Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) ell ∧
        (z ^ 2 + 1) * Polynomial.eval₂ (algebraMap ℤ ℂ) z R =
            z * Polynomial.eval₂ (algebraMap ℤ ℂ) z A +
              Polynomial.eval₂ (algebraMap ℤ ℂ) z A.reverse ∧
        (z - 1) * Polynomial.eval₂ (algebraMap ℤ ℂ) z P₁ =
            z * Polynomial.eval₂ (algebraMap ℤ ℂ) z A -
              Polynomial.eval₂ (algebraMap ℤ ℂ) z A.reverse ∧
        (z - 1) * Polynomial.eval₂ (algebraMap ℤ ℂ) z P₂ =
            z ^ 2 * Polynomial.eval₂ (algebraMap ℤ ℂ) z A -
              Polynomial.eval₂ (algebraMap ℤ ℂ) z A.reverse ∧
        Polynomial.eval₂ (algebraMap ℤ ℂ) z P₁ =
            (z + 1) * z ^ n *
              Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) q ∧
        Polynomial.eval₂ (algebraMap ℤ ℂ) z P₂ =
            z ^ (n + 1) *
              Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) r)

/-- Claim 9291: the reciprocal trace lift is the ordinary integral polynomial
whose nonzero complex evaluations have the displayed form. -/
def claim9291_reciprocalTraceLift : Prop :=
  ∀ (n : ℕ) (f : ℤ[X]), f.natDegree ≤ n →
    ∃! R : ℤ[X],
      ∀ z : ℂ, z ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ℂ) z R =
          z ^ n * Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) f

/-- Claim 9295: the first auxiliary trace polynomial has the target's parity. -/
def claim9295_targetAuxiliaryParity : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]),
    claim9292_typeIVDatum n ell R A P₁ P₂ q r →
      q.map (algebraMap ℤ (ZMod 2)) =
        ell.map (algebraMap ℤ (ZMod 2))

/-- Claim 9296: the integral affine correction exists uniquely and gives the
second auxiliary trace. -/
def claim9296_uniqueIntegralCorrection : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]),
    claim9292_typeIVDatum n ell R A P₁ P₂ q r →
      ∃! c : ℤ[X],
        c.natDegree ≤ n - 1 ∧
        ell = q + Polynomial.C (2 : ℤ) * c ∧
        r = (Polynomial.X + Polynomial.C (1 : ℤ)) * q + Polynomial.X * c

/-- Claim 9297: the Boyd polynomial is the affine expression in the unique
correction. -/
def claim9297_affineBoydPolynomial : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r c : ℤ[X]),
    claim9292_typeIVDatum n ell R A P₁ P₂ q r →
    c.natDegree ≤ n - 1 →
    ell = q + Polynomial.C (2 : ℤ) * c →
    r = (Polynomial.X + Polynomial.C (1 : ℤ)) * q + Polynomial.X * c →
      ∀ z : ℂ, z ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ℂ) z A =
          z ^ n *
            (z * Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) q +
              (z + z⁻¹) * Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) c)

/-- Claim 9298: the affine equations and the trace evaluations are reversible
for the type-IV identities. -/
def claim9298_affineParameterizationReversible : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]),
    ell.Monic → A.Monic → A.natDegree = 2 * n + 1 →
      (claim9292_typeIVDatum n ell R A P₁ P₂ q r ↔
        ∃ c : ℤ[X],
          c.natDegree ≤ n - 1 ∧
          ell = q + Polynomial.C (2 : ℤ) * c ∧
          r = (Polynomial.X + Polynomial.C (1 : ℤ)) * q + Polynomial.X * c ∧
          (∀ z : ℂ, z ≠ 0 →
            Polynomial.eval₂ (algebraMap ℤ ℂ) z R =
                z ^ n * Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) ell ∧
            Polynomial.eval₂ (algebraMap ℤ ℂ) z A =
                z ^ n *
                  (z * Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) q +
                    (z + z⁻¹) *
                      Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) c) ∧
            Polynomial.eval₂ (algebraMap ℤ ℂ) z P₁ =
                (z + 1) * z ^ n *
                  Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) q ∧
            Polynomial.eval₂ (algebraMap ℤ ℂ) z P₂ =
                z ^ (n + 1) *
                  Polynomial.eval₂ (algebraMap ℤ ℂ) (z + z⁻¹) r))

/-- Claim 9299: the auxiliary resultant has the displayed square factor. -/
def claim9299_auxiliaryResultantSquare : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]),
    claim9292_typeIVDatum n ell R A P₁ P₂ q r →
      Polynomial.resultant P₁ P₂ =
        (-1 : ℤ) ^ (n + 1) * r.eval (-2) *
          (Polynomial.resultant q r) ^ 2

/-- Claim 9300: the auxiliary and reciprocal resultants are joined without a
spurious division. -/
def claim9300_reciprocalResultantBridge : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]),
    claim9292_typeIVDatum n ell R A P₁ P₂ q r →
      A.eval 1 * Polynomial.resultant P₁ P₂ =
        Polynomial.resultant A A.reverse

/-- Claim 9301: the two endpoint evaluations of the type-IV data. -/
def claim9301_endpointEvaluations : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]),
    claim9292_typeIVDatum n ell R A P₁ P₂ q r →
      A.eval 1 = ell.eval 2 ∧ r.eval (-2) = -ell.eval (-2)

/-- Claim 9302: combining the endpoint and resultant identities gives the
endpoint-square factorization. -/
def claim9302_endpointSquareResultantFactorization : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]),
    claim9292_typeIVDatum n ell R A P₁ P₂ q r →
      Polynomial.resultant A A.reverse =
        (-1 : ℤ) ^ n * ell.eval 2 * ell.eval (-2) *
          (Polynomial.resultant q r) ^ 2

/-- Claim 9303: the exact resultant identity obtained by evaluating at roots
of `q`. -/
def claim9303_qrEllResultantIdentity : Prop :=
  ∀ (n : ℕ) (ell R A P₁ P₂ q r : ℤ[X]),
    claim9292_typeIVDatum n ell R A P₁ P₂ q r →
      (2 : ℤ) ^ n * Polynomial.resultant q r =
        (-1 : ℤ) ^ n * q.eval 0 * Polynomial.resultant q ell

end MathlibPlus.Open.Algebra
