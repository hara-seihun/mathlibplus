import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-!
# Degree-p divisor downsets

Faithful registry formalization of admitted claim 38543.  Natural-valued
exponents index the monomials, and the positive exponent multiset is formed
by filtering the finite index type before mapping the exponent function.
-/

/-- Claim 38543: the degree-`p` divisor-downset lower bound, its equality
criterion, and the resulting count for every finite divisor downset. -/
def divisorDownsetLowerBound : Prop :=
  ∀ (d p : ℕ) (a : Fin d → ℕ),
    (∑ i, a i) = p →
    (∀ i, a i ≤ p - 1) →
    2 ≤ (Finset.univ.filter (fun i => 0 < a i)).card →
    2 * p - 1 ≤ (∏ i, (a i + 1)) - 1 ∧
      ((∏ i, (a i + 1)) - 1 = 2 * p - 1 ↔
        (Finset.univ.filter (fun i => 0 < a i)).val.map a =
          ({p - 1, 1} : Multiset ℕ)) ∧
      (∀ D : Finset (Fin d → ℕ),
        a ∈ D →
        (∀ u ∈ D, ∀ v : Fin d → ℕ, (∀ i, v i ≤ u i) → v ∈ D) →
        2 * p - 1 ≤
          (D.filter (fun u => ∃ i, u i ≠ 0)).card)

end MathlibPlus.Open.Combinatorics
