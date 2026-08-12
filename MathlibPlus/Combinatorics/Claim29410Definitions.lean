import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Multiset.Basic

namespace MathlibPlus.Combinatorics.Claim29410

open scoped BigOperators

/-- The contribution of one positive leg of length `a`, with variables `0 = u`
and `1 = z`. -/
noncomputable def legMessage (a : ℕ) : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.X 0 ^ a +
    MvPolynomial.X 1 * (∑ k ∈ Finset.Ico 1 a, MvPolynomial.X 0 ^ k)

/-- The rooted side message, summing with multiset multiplicity. -/
noncomputable def rootedSideMessage (C : Multiset ℕ) : MvPolynomial (Fin 2) ℕ :=
  (C.map legMessage).sum

end MathlibPlus.Combinatorics.Claim29410
