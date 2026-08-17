import Mathlib
import MathlibPlus.Open.ResearchFormalization.BoydAffineBatch
import MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

namespace MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

/-- The exact integral Boyd data: reciprocal polynomial, trace lift, Boyd
identity, both auxiliary identities, correction equations, reconstruction, and
resultant factorization are all retained. -/
def typeIVDatum
    (n : ℕ) (ell A Astar R P1 P2 q r c : Polynomial ℤ) : Prop :=
  ell.Monic ∧
    A.Monic ∧
    A.natDegree = 2 * n + 1 ∧
    Astar = A.reverse ∧
    (∀ z : ℂ, z ≠ 0 →
      evalIntComplex R z = z ^ n * evalIntComplex ell (z + z⁻¹)) ∧
    (∀ z : ℂ, z ≠ 0 →
      (z ^ 2 + 1) * evalIntComplex R z =
        z * evalIntComplex A z + evalIntComplex Astar z) ∧
    (∀ z : ℂ, z ≠ 0 →
      (z - 1) * evalIntComplex P1 z =
        z * evalIntComplex A z - evalIntComplex Astar z) ∧
    (∀ z : ℂ, z ≠ 0 →
      (z - 1) * evalIntComplex P2 z =
        z ^ 2 * evalIntComplex A z - evalIntComplex Astar z) ∧
    (∀ z : ℂ, z ≠ 0 →
      evalIntComplex P1 z =
        (z + 1) * z ^ n * evalIntComplex q (z + z⁻¹)) ∧
    (∀ z : ℂ, z ≠ 0 →
      evalIntComplex P2 z =
        z ^ (n + 1) * evalIntComplex r (z + z⁻¹)) ∧
    c.degree ≤ (n - 1 : ℕ) ∧
    ell = q + Polynomial.C (2 : ℤ) * c ∧
    r = (Polynomial.X + Polynomial.C (1 : ℤ)) * q + Polynomial.X * c ∧
    2 * r - (Polynomial.X + Polynomial.C (2 : ℤ)) * q =
      Polynomial.X * ell ∧
    (∀ z : ℂ, z ≠ 0 →
      evalIntComplex A z = z ^ n *
        (z * evalIntComplex q (z + z⁻¹) +
          (z + z⁻¹) * evalIntComplex c (z + z⁻¹))) ∧
    Polynomial.resultant A Astar =
      (-1 : ℤ) ^ n * Polynomial.eval 2 ell *
        Polynomial.eval (-2) ell * (Polynomial.resultant q r) ^ 2

/-- The trace polynomial is a Salem target in the reviewed reciprocal-trace
carrier, rather than merely a monic polynomial with a convenient name. -/
def salemTraceTarget (ell : Polynomial ℤ) : Prop :=
  ∃ R : Polynomial ℤ,
    isSalemPolynomial R 5 ∧ traceLift R ell 5

/-- The genuine Type-IV auxiliary carrier: the poles of q/r consist of n
ordered interior roots of r with positive residues and one exterior root with a
negative residue; the Salem trace root lies between 2 and that exterior pole. -/
def typeIVAuxiliaryInterlacing
    (n : ℕ) (ell q r : Polynomial ℤ) : Prop :=
  let ellR := ell.map (algebraMap ℤ ℝ)
  let qR := q.map (algebraMap ℤ ℝ)
  let rR := r.map (algebraMap ℤ ℝ)
  qR.Monic ∧
    rR.Monic ∧
      qR.natDegree = n ∧ rR.natDegree = n + 1 ∧
        ∃ u : Fin n → ℝ, ∃ b : ℝ,
          StrictMono u ∧
            (∀ i : Fin n,
              -2 < u i ∧ u i < 2 ∧
                Polynomial.eval (u i) rR = 0 ∧
                  0 < Polynomial.eval (u i) qR /
                    Polynomial.eval (u i) rR.derivative) ∧
              2 < b ∧ Polynomial.eval b rR = 0 ∧
                Polynomial.eval b qR /
                    Polynomial.eval b rR.derivative < 0 ∧
                  (∀ z : ℂ, evalRealComplex rR z = 0 →
                    (∃ i : Fin n, z = (u i : ℂ)) ∨ z = (b : ℂ)) ∧
                    ∃ T : ℝ,
                      2 < T ∧ T < b ∧ Polynomial.eval T ellR = 0 ∧
                        ∀ s : ℝ, 2 < s → s < b →
                          Polynomial.eval s ellR = 0 → s = T

/-- A genuine witness includes the complete Type-IV auxiliary interlacing and
Pisot conditions in addition to the polynomial identities. -/
def genuineTypeIVWitness
    (n : ℕ) (ell A Astar R P1 P2 q r c : Polynomial ℤ) : Prop :=
  (isSalemPolynomial R n ∧ traceLift R ell n) ∧
    typeIVDatum n ell A Astar R P1 P2 q r c ∧
      pisotPolynomial A ∧ typeIVAuxiliaryInterlacing n ell q r

/-- The fixed Lehmer trace polynomial and the two reviewed corrections. -/
def lehmerTarget : Polynomial ℤ :=
  Polynomial.X ^ 5 + Polynomial.X ^ 4 - 5 * Polynomial.X ^ 3 -
    5 * Polynomial.X ^ 2 + 4 * Polynomial.X + 3

def firstCorrection : Polynomial ℤ :=
  Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 - Polynomial.X

def secondCorrection : Polynomial ℤ :=
  Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 1

/-- Claim 42195: the fixed Salem target has two genuine Type-IV Boyd Pisot
witnesses with unequal raw reciprocal resultant absolute values. -/
def claim42195 : Prop :=
  salemTraceTarget lehmerTarget ∧
    ∃ (A₁ Astar₁ R₁ P₁₁ P₂₁ q₁ r₁
        A₂ Astar₂ R₂ P₁₂ P₂₂ q₂ r₂ : Polynomial ℤ),
      genuineTypeIVWitness 5 lehmerTarget A₁ Astar₁ R₁ P₁₁ P₂₁ q₁ r₁
        firstCorrection ∧
        genuineTypeIVWitness 5 lehmerTarget A₂ Astar₂ R₂ P₁₂ P₂₂ q₂ r₂
          secondCorrection ∧
          Int.natAbs (Polynomial.resultant A₁ Astar₁) ≠
            Int.natAbs (Polynomial.resultant A₂ Astar₂)

end

end MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair
