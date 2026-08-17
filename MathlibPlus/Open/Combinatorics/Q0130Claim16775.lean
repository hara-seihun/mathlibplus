import Mathlib
import MathlibPlus.Combinatorics.StrongOrdering

namespace MathlibPlus.Open.Combinatorics.Q0130

noncomputable section

open MathlibPlus.Combinatorics

/-- The prefix set, including the initial zero, of a label list. -/
def pathPrefixSet {G : Type*} [AddCommGroup G] (B : List G) : Set G :=
  {x | x ∈ List.scanl (fun s a => s + a) 0 B}

/-- The total of a strong path. -/
def pathTotal {G : Type*} [AddCommGroup G] (B : List G) : G :=
  B.sum

/-- An unused label is a member of the ambient label set but not of the path. -/
def unusedPathLabel {G : Type*} [AddCommGroup G]
    (A : Finset G) (B : List G) (u : G) : Prop :=
  u ∈ A ∧ u ∉ B

/-- The two reflected prefix carriers in the insertion-maximal trap. -/
def negatedPathPrefixSet {G : Type*} [AddCommGroup G]
    (B : List G) : Set G :=
  {u | ∃ x ∈ pathPrefixSet B, u = -x}

def translatedPathPrefixSet {G : Type*} [AddCommGroup G]
    (B : List G) : Set G :=
  {u | ∃ x ∈ pathPrefixSet B, u = x - pathTotal B}

/-- The exact strong-path and all-cut insertion-maximality context. -/
def insertionMaximalStrongPath {G : Type*} [AddCommGroup G]
    (A : Finset G) (B : List G) : Prop :=
  0 ∉ A ∧
    B.Nodup ∧
      (∀ x ∈ B, x ∈ A) ∧
        strongOrdering B ∧
          ∀ u, unusedPathLabel A B u →
            ∀ k : ℕ, k ≤ B.length →
              ¬ strongOrdering (B.take k ++ [u] ++ B.drop k)

/-- Claim 16775: every unused label in an insertion-maximal strong path is
in both the negative prefix carrier and the prefix carrier translated by the
path total. -/
def insertionMaximalPrefixTrap_claim16775 : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (A : Finset G) (B : List G),
    insertionMaximalStrongPath A B →
      ∀ u, unusedPathLabel A B u →
        u ∈ negatedPathPrefixSet B ∧ u ∈ translatedPathPrefixSet B

end

end MathlibPlus.Open.Combinatorics.Q0130
