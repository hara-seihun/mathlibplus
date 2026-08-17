import Mathlib
import MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

namespace MathlibPlus.Open.ResearchFormalization.R2654ReconstructionClaim42186

noncomputable section

open MathlibPlus.Open.ResearchFormalization

/-- The displayed trace expression for the reconstructed polynomial member. -/
def reconstructionFormula
    (n : ℕ) (q c A : Polynomial ℤ) : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    evalIntComplex A z = z ^ n *
      (z * evalIntComplex q (z + z⁻¹) +
        (z + z⁻¹) * evalIntComplex c (z + z⁻¹))

/-- Boyd's identity for a polynomial and its actual reciprocal. -/
def boydIdentity
    (R A : Polynomial ℤ) : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    (z ^ 2 + 1) * evalIntComplex R z =
      z * evalIntComplex A z + evalIntComplex A.reverse z

/-- The reviewed reciprocal-trace input together with the monic auxiliary
polynomials and the exact correction equations. -/
def correctionInput
    (n : ℕ) (ell R q r c : Polynomial ℤ) : Prop :=
  traceLift R ell n ∧
    q.Monic ∧
    r.Monic ∧
    c.degree ≤ (n - 1 : ℕ) ∧
    ell = q + Polynomial.C (2 : ℤ) * c ∧
    r = (Polynomial.X + Polynomial.C (1 : ℤ)) * q +
      Polynomial.X * c

/-- A reconstructed Boyd member is an actual integral polynomial of the
specified degree, with the displayed formula and the original reciprocal
identity. -/
def reconstructedBoydWitness
    (n : ℕ) (R q c : Polynomial ℤ) : Prop :=
  ∃ A : Polynomial ℤ,
    A.Monic ∧
      A.natDegree = 2 * n + 1 ∧
        reconstructionFormula n q c A ∧
          boydIdentity R A

/-- Claim 42186: the two exact correction equations reconstruct a Boyd
witness and recover the original Boyd identity. -/
def claim42186 : Prop :=
  ∀ (n : ℕ) (ell R q r c : Polynomial ℤ),
    correctionInput n ell R q r c →
      reconstructedBoydWitness n R q c

end

end MathlibPlus.Open.ResearchFormalization.R2654ReconstructionClaim42186
