import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0130Claim16782

noncomputable section

/-- Prefixes of a path, including the initial zero. -/
def pathPrefixes {G : Type*} [AddMonoid G] (xs : List G) : List G :=
  xs.scanl (fun s x => s + x) 0

/-- A strong path has distinct labels from the ambient finite set and distinct
prefixes including the initial zero. -/
def strongPath {G : Type*} [AddMonoid G] [DecidableEq G]
    (A : Finset G) (xs : List G) : Prop :=
  xs.Nodup ∧ xs.toFinset ⊆ A ∧ (pathPrefixes xs).Nodup

/-- The labels not used by a path. -/
def unusedLabels {G : Type*} [AddMonoid G] [DecidableEq G]
    (A : Finset G) (xs : List G) : Finset G :=
  A \ xs.toFinset

/-- Insertion-maximality for the strong path. -/
def insertionMaximal {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (xs : List G) : Prop :=
  strongPath A xs ∧
    ∀ w ∈ unusedLabels A xs, ∀ i ≤ xs.length,
      ¬ strongPath A (xs.take i ++ [w] ++ xs.drop i)

/-- A pair of unused labels reflected about the path total. -/
def reflectedPair {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (xs : List G) (u v : G) : Prop :=
  u ∈ unusedLabels A xs ∧
    v ∈ unusedLabels A xs ∧
      u ≠ v ∧ u + v = -xs.sum

/-- Replacing one used edge by the two reflected labels. -/
def edgeSplice {G : Type*} (xs : List G) (u v : G) (i : ℕ) : List G :=
  xs.take i ++ [u, v] ++ xs.drop (i + 1)

/-- Failure of every concrete used-edge replacement by the reflected pair. -/
def spliceSuccessful {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (xs : List G) (u v : G) : Prop :=
  ∃ i : ℕ, i < xs.length ∧ strongPath A (edgeSplice xs u v i)

/-- The total of the first i labels, with the natural path-prefix meaning. -/
def prefixValue {G : Type*} [AddMonoid G] (xs : List G) (i : ℕ) : G :=
  (xs.take i).sum

/-- The central failed-splice setup: an insertion-maximal strong path, a
nonfixed reflected unused pair, its two complementary cuts, and three
nonempty consecutive blocks. -/
def centralFailedSplice {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (xs : List G) (u v : G)
    (L M R : List G) : Prop :=
  insertionMaximal A xs ∧
    reflectedPair A xs u v ∧
      u + u - v = 0 ∧
      xs = L ++ M ++ R ∧
      L ≠ [] ∧ M ≠ [] ∧ R ≠ [] ∧
      prefixValue xs L.length = -u ∧
      prefixValue xs (L.length + M.length) = -v ∧
      ¬ spliceSuccessful A xs u v

/-- Claim 16782: in the central case the total and all three nonempty
consecutive block sums are fixed; there is at most one reflected pair away
from characteristic three, while characteristic three forces total zero. -/
def claim16782 : Prop :=
  ∀ p : ℕ, p.Prime →
    ∀ (A : Finset (ZMod p)) (xs : List (ZMod p))
      (u v : ZMod p) (L M R : List (ZMod p)),
      centralFailedSplice A xs u v L M R →
        xs.sum = -(u + u + u) ∧
          L.sum = -u ∧ M.sum = -u ∧ R.sum = -u ∧
          (p ≠ 3 →
            ∀ (u' v' : ZMod p) (L' M' R' : List (ZMod p)),
              centralFailedSplice A xs u' v' L' M' R' →
                ({u', v'} : Finset (ZMod p)) = {u, v}) ∧
          (p = 3 → xs.sum = 0)

end

end MathlibPlus.Open.ResearchFormalization.BatchQ0130Claim16782
