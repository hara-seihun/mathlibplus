import Mathlib
import MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

namespace MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

/-- The exact R-2654 type-IV hypotheses, with the terminal resultant identity
left as the conclusion of Claim 42187 rather than assumed in its carrier. -/
def resultantFactorizationHypotheses
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
          (z + z⁻¹) * evalIntComplex c (z + z⁻¹)))

/-- Claim 42187: every associated R-2654 type-IV datum satisfies the exact
reciprocal-resultant factorization, with Mathlib's resultant convention and
integer endpoint evaluations. -/
def claim42187 : Prop :=
  ∀ (n : ℕ) (ell A Astar R P1 P2 q r c : Polynomial ℤ),
    resultantFactorizationHypotheses n ell A Astar R P1 P2 q r c →
      Polynomial.resultant A Astar =
        (-1 : ℤ) ^ n * Polynomial.eval 2 ell *
          Polynomial.eval (-2) ell * (Polynomial.resultant q r) ^ 2

end

end MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair
