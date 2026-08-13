import Mathlib

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators

universe u

/--
The arithmetic rank-polynomial form of rank symmetry and unimodality for the
edge poset of a regular finite-abelian Boolean quotient.  For a finite abelian
group `Γ`, `orderCount L` counts elements of exact order `L`; `removed k` is
the coefficient lost from `(1 + X)^(|Γ|-1)` through the arithmetic
reflection-pair fibres.
-/
def regularAbelianBooleanEdgeRankUnimodality : Prop :=
  ∀ (Γ : Type u) [Fintype Γ] [CommGroup Γ],
    let n := Fintype.card Γ
    let orderCount : ℕ → ℕ := fun l =>
      Fintype.card {g : Γ // orderOf g = l}
    let removed : ℕ → ℕ := fun k =>
      ∑ l ∈ Finset.Icc 3 n,
        if l ∣ n ∧ 0 < k % l ∧ k % l + 1 < l then
          (orderCount l / 2) * Nat.choose (n / l - 1) (k / l)
        else
          0
    let edgeRank : ℕ → ℕ := fun k => Nat.choose (n - 1) k - removed k
    (∀ k ≤ n - 1, edgeRank k = edgeRank (n - 1 - k)) ∧
      ∀ k, 2 * k + 2 < n → edgeRank k ≤ edgeRank (k + 1)

end MathlibPlus.Open.Combinatorics
