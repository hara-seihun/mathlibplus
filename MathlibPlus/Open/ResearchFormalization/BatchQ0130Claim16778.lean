import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0130Claim16778

noncomputable section

/-- The prefix list of a labelled path, including the initial zero. -/
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

/-- Inserting an unused label at a cut of the path. -/
def insertAt {G : Type*} (xs : List G) (u : G) (i : ℕ) : List G :=
  xs.take i ++ [u] ++ xs.drop i

/-- No unused label can be inserted at any cut while retaining a strong path. -/
def insertionMaximal {G : Type*} [AddMonoid G] [DecidableEq G]
    (A : Finset G) (xs : List G) : Prop :=
  strongPath A xs ∧
    ∀ u ∈ unusedLabels A xs, ∀ i ≤ xs.length,
      ¬ strongPath A (insertAt xs u i)

/-- Unused labels which occur in a reflected unused pair for the path total. -/
def reflectedUnusedLabels {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (xs : List G) : Finset G :=
  unusedLabels A xs ∩
    (unusedLabels A xs).image (fun u => -xs.sum - u)

/-- Claim 16778: an insertion-maximal strong path with no unused reflected
pair has the two-thirds lower bound. -/
def claim16778 : Prop :=
  ∀ {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (xs : List G),
    insertionMaximal A xs →
      reflectedUnusedLabels A xs = ∅ →
        3 * xs.length ≥ 2 * A.card - 1

end

end MathlibPlus.Open.ResearchFormalization.BatchQ0130Claim16778
