import Mathlib

namespace MathlibPlus.Open.Arithmetic

/-- For every prime at most 29, every subset of the nonzero residue classes admits
an ordering whose nonempty partial sums are pairwise distinct. -/
def smallPrimeSubsetDistinctPartialSums : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ≤ 29 →
    ∀ A : Finset (ZMod p),
      (∀ a ∈ A, a ≠ 0) →
      ∃ l : List (ZMod p),
        l.toFinset = A ∧
          l.Nodup ∧
            (l.scanl (fun s a => s + a) (0 : ZMod p)).tail.Pairwise (fun x y => x ≠ y)

end MathlibPlus.Open.Arithmetic
