import Mathlib
import MathlibPlus.Open.Algebra.TypeIVFormalizationBatch
import MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

namespace MathlibPlus.Open.ResearchFormalization.R2654AffineResultant

noncomputable section

open MathlibPlus.Open.Algebra
open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

/-- The algebraic Boyd carrier from the reciprocal trace and auxiliary
factorizations, together with the integral correction equations.  It omits
resultant conclusions so those remain conclusions of the leased claims. -/
def affineBoydDatum
    (n : ℕ) (ell R A P1 P2 q r c : Polynomial ℤ) : Prop :=
  claim9292_typeIVDatum n ell R A P1 P2 q r ∧
    c.degree ≤ (n - 1 : ℕ) ∧
      ell = q + Polynomial.C (2 : ℤ) * c ∧
        r = (Polynomial.X + Polynomial.C (1 : ℤ)) * q +
          Polynomial.X * c

/-- Claim 42188: the two forms of the refined auxiliary resultant identity
hold in the reciprocal-trace Boyd carrier. -/
def claim42188 : Prop :=
  ∀ (n : ℕ) (ell R A P1 P2 q r : Polynomial ℤ),
    claim9292_typeIVDatum n ell R A P1 P2 q r →
      Polynomial.resultant P1 P2 =
          (-1 : ℤ) ^ (n + 1) * Polynomial.eval (-2) r *
            (Polynomial.resultant q r) ^ 2 ∧
        (-1 : ℤ) ^ (n + 1) * Polynomial.eval (-2) r *
            (Polynomial.resultant q r) ^ 2 =
          Polynomial.resultant A A.reverse / Polynomial.eval 1 A

/-- Claim 42189: the auxiliary resultants of q and r and of q and the target
trace are related by the displayed signed power-of-two identity. -/
def claim42189 : Prop :=
  ∀ (n : ℕ) (ell R A P1 P2 q r : Polynomial ℤ),
    claim9292_typeIVDatum n ell R A P1 P2 q r →
      (2 : ℤ) ^ n * Polynomial.resultant q r =
        (-1 : ℤ) ^ n * Polynomial.eval 0 q *
          Polynomial.resultant q ell

/-- Claim 42192: an integral, degree-bounded increment of the correction
polynomial gives the stated transformed q, r, and A, while retaining the
same target and the full Boyd carrier. -/
def claim42192 : Prop :=
  ∀ (n : ℕ) (ell R A P1 P2 q r c : Polynomial ℤ),
    affineBoydDatum n ell R A P1 P2 q r c →
      ∀ d : Polynomial ℤ,
        d.degree ≤ (n - 1 : ℕ) →
          ∃ (A' P1' P2' : Polynomial ℤ),
            affineBoydDatum n ell R A' P1' P2'
                (q - Polynomial.C (2 : ℤ) * d)
                (r - (Polynomial.X + Polynomial.C (2 : ℤ)) * d)
                (c + d) ∧
              (∀ z : ℂ, z ≠ 0 →
                evalIntComplex A' z =
                  evalIntComplex A z +
                    z ^ (n - 1) * (1 - z ^ 2) *
                      evalIntComplex d (z + z⁻¹))

/-- The two exact degree-eleven Boyd polynomials obtained from the displayed
Lehmer target and the two displayed corrections by the converse reconstruction
formula. -/
def lehmerWitnessA₁ : Polynomial ℤ :=
  Polynomial.X ^ 11 - 2 * Polynomial.X ^ 9 - 4 * Polynomial.X ^ 8 -
    4 * Polynomial.X ^ 7 - 3 * Polynomial.X ^ 6 - Polynomial.X ^ 5 +
    Polynomial.X ^ 4 + 3 * Polynomial.X ^ 3 + 4 * Polynomial.X ^ 2 +
    3 * Polynomial.X + 1

def lehmerWitnessA₂ : Polynomial ℤ :=
  Polynomial.X ^ 11 - 2 * Polynomial.X ^ 9 - 4 * Polynomial.X ^ 8 -
    5 * Polynomial.X ^ 7 - 4 * Polynomial.X ^ 6 - Polynomial.X ^ 5 +
    2 * Polynomial.X ^ 4 + 4 * Polynomial.X ^ 3 + 4 * Polynomial.X ^ 2 +
    3 * Polynomial.X + 1

/-- Claim 42194: the two exact Lehmer-target witnesses have the two displayed
absolute reciprocal-resultant values. -/
def claim42194 : Prop :=
  ∃ (R₁ P₁₁ P₂₁ q₁ r₁ R₂ P₁₂ P₂₂ q₂ r₂ : Polynomial ℤ),
    genuineTypeIVWitness 5 lehmerTarget lehmerWitnessA₁
        lehmerWitnessA₁.reverse R₁ P₁₁ P₂₁ q₁ r₁ firstCorrection ∧
      genuineTypeIVWitness 5 lehmerTarget lehmerWitnessA₂
        lehmerWitnessA₂.reverse R₂ P₁₂ P₂₂ q₂ r₂ secondCorrection ∧
      Int.natAbs
          (Polynomial.resultant lehmerWitnessA₁ lehmerWitnessA₁.reverse) = 81 ∧
        Int.natAbs
            (Polynomial.resultant lehmerWitnessA₂ lehmerWitnessA₂.reverse) = 169

end

end MathlibPlus.Open.ResearchFormalization.R2654AffineResultant
