import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch.Arithmetic

noncomputable section
open Set

/-- Claim 18981: two prime logarithms in one cyclic additive lattice force
 the primes to agree. -/
def claim_18981 : Prop :=
  ∀ p r : ℕ, Nat.Prime p → Nat.Prime r →
    (∃ (a : ℝ) (m n : ℤ),
      Real.log (p : ℝ) = a * (m : ℝ) ∧
      Real.log (r : ℝ) = a * (n : ℝ)) →
    p = r

/-- The rational primes whose logarithms lie in one of finitely many cyclic
lattices. -/
def primesInCyclicLogLattices (N : ℕ) (a : Fin N → ℝ) : Set ℕ :=
  {p | Nat.Prime p ∧
    ∃ (i : Fin N) (m : ℤ), Real.log (p : ℝ) = a i * (m : ℝ)}

/-- Claim 18982: a finite union of N cyclic logarithmic lattices contains at
most N prime logarithms and therefore misses a rational prime logarithm. -/
def claim_18982 : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ),
    Set.Finite (primesInCyclicLogLattices N a) ∧
    (primesInCyclicLogLattices N a).ncard ≤ N ∧
    ∃ p : ℕ, Nat.Prime p ∧ p ∉ primesInCyclicLogLattices N a

end
end MathlibPlus.Open.Research.FormalizationBatch.Arithmetic
