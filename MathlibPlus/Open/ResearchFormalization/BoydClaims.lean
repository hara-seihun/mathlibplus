import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalizationBatch

/-- The complex evaluation of an integral polynomial. -/
noncomputable def complexEval (p : Polynomial ℤ) (z : ℂ) : ℂ :=
  Polynomial.eval z (p.map (Int.castRingHom ℂ))

/-- Claim 9291: the reciprocal trace expression is represented by an ordinary
polynomial.  The equality is written on the nonzero complex numbers so that
`z⁻¹` has its literal meaning. -/
def claim9291 : Prop :=
  ∀ n : ℕ, ∀ f : Polynomial ℤ,
    f.degree ≤ (n : WithBot ℕ) →
      ∃ R : Polynomial ℤ, ∀ z : ℂ, z ≠ 0 →
        complexEval R z = z ^ n * complexEval f (z + z⁻¹)

/-- Exact polynomial data and trace identities used by the type-IV claims. -/
def isTypeIVDatum
    (n : ℕ) (ell A Astar R P1 P2 q r : Polynomial ℤ) : Prop :=
  ell.Monic ∧
    A.Monic ∧
    A.natDegree = 2 * n + 1 ∧
    (∀ z : ℂ, z ≠ 0 →
      complexEval Astar z = z ^ (2 * n + 1) * complexEval A (z⁻¹)) ∧
    (∀ z : ℂ, z ≠ 0 →
      complexEval R z = z ^ n * complexEval ell (z + z⁻¹)) ∧
    (∀ z : ℂ, z ≠ 0 →
      (z ^ 2 + 1) * complexEval R z =
        z * complexEval A z + complexEval Astar z) ∧
    (∀ z : ℂ, z ≠ 0 →
      (z - 1) * complexEval P1 z =
        z * complexEval A z - complexEval Astar z) ∧
    (∀ z : ℂ, z ≠ 0 →
      (z - 1) * complexEval P2 z =
        z ^ 2 * complexEval A z - complexEval Astar z) ∧
    (∀ z : ℂ, z ≠ 0 →
      complexEval P1 z =
        (z + 1) * z ^ n * complexEval q (z + z⁻¹)) ∧
    (∀ z : ℂ, z ≠ 0 →
      complexEval P2 z =
        z ^ (n + 1) * complexEval r (z + z⁻¹))

/-- Claim 9295: every coefficient of ell-q is even. -/
def claim9295 : Prop :=
  ∀ n : ℕ, ∀ ell A Astar R P1 P2 q r : Polynomial ℤ,
    isTypeIVDatum n ell A Astar R P1 P2 q r →
      ∀ i : ℕ, Even ((ell - q).coeff i)

/-- Claim 9296: the integral affine correction is unique and gives the second
trace. -/
def claim9296 : Prop :=
  ∀ n : ℕ, ∀ ell A Astar R P1 P2 q r : Polynomial ℤ,
    isTypeIVDatum n ell A Astar R P1 P2 q r →
      (∃! c : Polynomial ℤ,
        c.degree ≤ (n - 1 : ℕ) ∧ ell = q + 2 * c) ∧
        (∀ c : Polynomial ℤ,
          c.degree ≤ (n - 1 : ℕ) → ell = q + 2 * c →
            r = (Polynomial.X + 1) * q + Polynomial.X * c)

/-- Claim 9297: the Boyd polynomial has the affine formula for the unique
correction. -/
def claim9297 : Prop :=
  ∀ n : ℕ, ∀ ell A Astar R P1 P2 q r : Polynomial ℤ,
    isTypeIVDatum n ell A Astar R P1 P2 q r →
      ∀ c : Polynomial ℤ,
        c.degree ≤ (n - 1 : ℕ) → ell = q + 2 * c →
          ∀ z : ℂ, z ≠ 0 →
            complexEval A z = z ^ n *
              (z * complexEval q (z + z⁻¹) +
                (z + z⁻¹) * complexEval c (z + z⁻¹))

/-- Claim 9299: the auxiliary resultant square identity. -/
def claim9299 : Prop :=
  ∀ n : ℕ, ∀ ell A Astar R P1 P2 q r : Polynomial ℤ,
    isTypeIVDatum n ell A Astar R P1 P2 q r →
      Polynomial.resultant P1 P2 =
        (-1 : ℤ) ^ (n + 1) * Polynomial.eval (-2) r *
          (Polynomial.resultant q r) ^ 2

/-- Claim 9300: the reciprocal-resultant bridge, in its division-free form. -/
def claim9300 : Prop :=
  ∀ n : ℕ, ∀ ell A Astar R P1 P2 q r : Polynomial ℤ,
    isTypeIVDatum n ell A Astar R P1 P2 q r →
      Polynomial.eval 1 A * Polynomial.resultant P1 P2 =
        Polynomial.resultant A Astar

/-- Claim 9301: the two endpoint evaluations. -/
def claim9301 : Prop :=
  ∀ n : ℕ, ∀ ell A Astar R P1 P2 q r : Polynomial ℤ,
    isTypeIVDatum n ell A Astar R P1 P2 q r →
      Polynomial.eval 1 A = Polynomial.eval 2 ell ∧
        Polynomial.eval (-2) r = -Polynomial.eval (-2) ell

/-- Claim 9302: the endpoint-square factorization of the reciprocal resultant. -/
def claim9302 : Prop :=
  ∀ n : ℕ, ∀ ell A Astar R P1 P2 q r : Polynomial ℤ,
    isTypeIVDatum n ell A Astar R P1 P2 q r →
      Polynomial.resultant A Astar =
        (-1 : ℤ) ^ n * Polynomial.eval 2 ell *
          Polynomial.eval (-2) ell * (Polynomial.resultant q r) ^ 2

/-- Claim 9303: the exact q-r-ell resultant identity. -/
def claim9303 : Prop :=
  ∀ n : ℕ, ∀ ell A Astar R P1 P2 q r : Polynomial ℤ,
    isTypeIVDatum n ell A Astar R P1 P2 q r →
      (2 : ℤ) ^ n * Polynomial.resultant q r =
        (-1 : ℤ) ^ n * Polynomial.eval 0 q *
          Polynomial.resultant q ell

end ResearchFormalizationBatch
end Open
end MathlibPlus
