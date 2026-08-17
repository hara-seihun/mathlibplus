import Mathlib

noncomputable section

namespace MathlibPlus.Open.Algebra

abbrev CubicField (p : ℕ) := ZMod p
abbrev CubicCyclic := ZMod 3
abbrev CubicSemidirectGroup (p : ℕ) := CubicField p × CubicCyclic
abbrev CubicModule (p : ℕ) := CubicField p × CubicField p
abbrev CubicPolynomialPair (p : ℕ) :=
  Polynomial (CubicField p) × Polynomial (CubicField p)

/-- The semidirect-product multiplication from S1. -/
def cubicSemidirectMul {p : ℕ} (omega : CubicField p)
    (x y : CubicSemidirectGroup p) : CubicSemidirectGroup p :=
  (x.1 + omega ^ x.2.val * y.1, x.2 + y.2)

/-- `tau(a,i) = (a^3,-3a^2)` from S1. -/
def cubicTau {p : ℕ} (x : CubicSemidirectGroup p) : CubicModule p :=
  (x.1 ^ 3, (-3 : CubicField p) * x.1 ^ 2)

def cubicHt {p : ℕ} (d t : CubicField p) : CubicSemidirectGroup p :=
  (d * t, 1)

def cubicKb {p : ℕ} (b : CubicField p) : CubicSemidirectGroup p :=
  (b, 0)

def cubicRelativeDefect {p : ℕ} (omega : CubicField p)
    (d t b : CubicField p) : CubicModule p :=
  cubicTau (cubicSemidirectMul omega (cubicHt d t) (cubicKb b)) -
    cubicTau (cubicHt d t) - omega • cubicTau (cubicKb b)

/-- The polynomial pair whose evaluation is the displayed relative defect. -/
def cubicRelativeDefectPolynomial {p : ℕ} (omega : CubicField p)
    (d t : CubicField p) : CubicPolynomialPair p :=
  (Polynomial.C (3 * d ^ 2 * t ^ 2 * omega) * Polynomial.X +
      Polynomial.C (3 * d * t * omega ^ 2) * Polynomial.X ^ 2 +
      Polynomial.C d * Polynomial.X ^ 3,
    Polynomial.C (-6 * d * t * omega) * Polynomial.X +
      Polynomial.C (-3 * (omega ^ 2 - omega)) * Polynomial.X ^ 2)

def evalCubicRelativeDefectPolynomial {p : ℕ}
    (P : CubicPolynomialPair p) (b : CubicField p) : CubicModule p :=
  (Polynomial.eval b P.1, Polynomial.eval b P.2)

/-- Claim 53451: under the prime, congruence, and nontrivial cube-root
hypotheses of S1, the exact relative derivative expansion in S2 holds, and
its cubic and quadratic coefficient vectors are the displayed ones. -/
def claim53451 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 3 = 1 →
    ∀ (omega : CubicField p),
      omega ^ 3 = 1 → omega ≠ (1 : CubicField p) →
      ∀ (t b : CubicField p),
        let d : CubicField p := 1 - omega
        let defect := cubicRelativeDefect omega d t b
        let polynomial := cubicRelativeDefectPolynomial omega d t
        defect.1 =
            3 * d ^ 2 * t ^ 2 * omega * b +
              3 * d * t * omega ^ 2 * b ^ 2 + d * b ^ 3 ∧
          defect.2 =
            -6 * d * t * omega * b -
              3 * (omega ^ 2 - omega) * b ^ 2 ∧
          evalCubicRelativeDefectPolynomial polynomial b = defect ∧
          (polynomial.1.coeff 3, polynomial.2.coeff 3) =
            (d, 0) ∧
          (polynomial.1.coeff 2, polynomial.2.coeff 2) =
            (3 * d * t * omega ^ 2, -3 * (omega ^ 2 - omega))

end MathlibPlus.Open.Algebra
