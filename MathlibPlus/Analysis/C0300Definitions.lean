import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis.C0300

noncomputable section

/-- The signed all-order aggregate from C-0300.  The source claim names the
channel family `H_r` but does not define its individual channels. -/
def signedAllOrderAggregate_claim4185
    (H : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' r : ℕ, x ^ r * H r x / (Nat.factorial r : ℝ)

/-- Vanishing to order at least `m` at a complex point. -/
def vanishesToOrderAtLeast_claim4192
    (f : ℂ → ℂ) (ρ : ℂ) (m : ℕ) : Prop :=
  ∀ k : ℕ, k < m → iteratedDeriv k f ρ = 0

/-- A zeta-zero occurrence carries its point and exact multiplicity.  The
pole at `1` is excluded, while no restriction to the critical strip is added,
so the trivial zeros remain in the carrier. -/
def zetaZeroOfMultiplicity_claim4192
    (ρ : ℂ) (m : ℕ) : Prop :=
  ρ ≠ 1 ∧
    riemannZeta ρ = 0 ∧
    0 < m ∧
    vanishesToOrderAtLeast_claim4192 riemannZeta ρ m ∧
    ¬ vanishesToOrderAtLeast_claim4192 riemannZeta ρ (m + 1)

structure ZetaZeroOccurrence_claim4192 where
  rho : ℂ
  multiplicity : ℕ
  isZero : zetaZeroOfMultiplicity_claim4192 rho multiplicity

/-- The first Cayley coordinate attached to a retained zeta-zero occurrence. -/
def cayleyA_claim4192 (z : ZetaZeroOccurrence_claim4192) : ℂ :=
  z.rho / (z.rho - 1)

/-- The shifted Cayley coordinate attached to the same occurrence. -/
def cayleyB_claim4192 (z : ZetaZeroOccurrence_claim4192) : ℂ :=
  cayleyA_claim4192 z - 1

/-- The exact two-coordinate relation in Claim 4192, over the retained
zero-with-multiplicity carrier. -/
def cayleyModeCoordinates_claim4192 : Prop :=
  ∀ z : ZetaZeroOccurrence_claim4192,
    cayleyA_claim4192 z = z.rho / (z.rho - 1) ∧
      cayleyB_claim4192 z = cayleyA_claim4192 z - 1 ∧
        cayleyB_claim4192 z = 1 / (z.rho - 1)

/-- The finite exponential tail, with the inclusive source endpoint
`2 ≤ r ≤ N`. -/
def truncatedExponentialTail_claim4193 (N : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.Icc 2 N, z ^ r / (r.factorial : ℂ)

/-- The infinite-order exponential tail with its first two terms removed. -/
def exponentialTail_claim4193 (z : ℂ) : ℂ :=
  Complex.exp z - 1 - z

/-- The displayed majorant for both the finite and infinite exponential
 tails, over the complex scalar carrier used by the C-0300 zero-pair and
Laplace formulas. -/
def truncatedExponentialMajorant_claim4194 : Prop :=
  ∀ (N : ℕ) (z : ℂ),
    ‖truncatedExponentialTail_claim4193 N z‖ ≤
        ‖z‖ ^ 2 * Real.exp ‖z‖ / 2 ∧
      ‖exponentialTail_claim4193 z‖ ≤
        ‖z‖ ^ 2 * Real.exp ‖z‖ / 2

end

end MathlibPlus.Analysis.C0300
