import MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

namespace MathlibPlus.Open.Algebra.Claim13310

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

/-- Claim 13310: the fixed Lehmer Salem target has two genuine Type-IV Boyd
witnesses obtained from the two named corrections, and their auxiliary (and
raw reciprocal) resultants are different. -/
def claim13310 : Prop :=
  let ell : Polynomial ℤ :=
    Polynomial.X ^ 5 + Polynomial.X ^ 4 - 5 * Polynomial.X ^ 3 -
      5 * Polynomial.X ^ 2 + 4 * Polynomial.X + 3
  let c₁ : Polynomial ℤ :=
    Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 - Polynomial.X
  let c₂ : Polynomial ℤ :=
    Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 1
  let q₁ : Polynomial ℤ :=
    Polynomial.X ^ 5 - Polynomial.X ^ 4 - 9 * Polynomial.X ^ 3 -
      5 * Polynomial.X ^ 2 + 6 * Polynomial.X + 3
  let r₁ : Polynomial ℤ :=
    Polynomial.X ^ 6 + Polynomial.X ^ 5 - 8 * Polynomial.X ^ 4 -
      14 * Polynomial.X ^ 3 + 9 * Polynomial.X + 3
  let q₂ : Polynomial ℤ :=
    Polynomial.X ^ 5 - Polynomial.X ^ 4 - 9 * Polynomial.X ^ 3 -
      5 * Polynomial.X ^ 2 + 4 * Polynomial.X + 1
  let r₂ : Polynomial ℤ :=
    Polynomial.X ^ 6 + Polynomial.X ^ 5 - 8 * Polynomial.X ^ 4 -
      14 * Polynomial.X ^ 3 - Polynomial.X ^ 2 + 6 * Polynomial.X + 1
  ∃ (R : Polynomial ℤ)
      (A₁ Astar₁ P₁₁ P₂₁ A₂ Astar₂ P₁₂ P₂₂ : Polynomial ℤ),
    isSalemPolynomial R 5 ∧
      traceLift R ell 5 ∧
      c₁ ≠ c₂ ∧
      q₁ + Polynomial.C (2 : ℤ) * c₁ = ell ∧
      r₁ = (Polynomial.X + Polynomial.C (1 : ℤ)) * q₁ + Polynomial.X * c₁ ∧
      q₂ + Polynomial.C (2 : ℤ) * c₂ = ell ∧
      r₂ = (Polynomial.X + Polynomial.C (1 : ℤ)) * q₂ + Polynomial.X * c₂ ∧
      Polynomial.resultant q₁ r₁ = (9 : ℤ) ∧
      Polynomial.resultant q₂ r₂ = (13 : ℤ) ∧
      genuineTypeIVWitness 5 ell A₁ Astar₁ R P₁₁ P₂₁ q₁ r₁ c₁ ∧
      genuineTypeIVWitness 5 ell A₂ Astar₂ R P₁₂ P₂₂ q₂ r₂ c₂ ∧
      Int.natAbs (Polynomial.resultant A₁ Astar₁) = (81 : ℕ) ∧
      Int.natAbs (Polynomial.resultant A₂ Astar₂) = (169 : ℕ) ∧
      Int.natAbs (Polynomial.resultant A₁ Astar₁) ≠
        Int.natAbs (Polynomial.resultant A₂ Astar₂)

end

end MathlibPlus.Open.Algebra.Claim13310
