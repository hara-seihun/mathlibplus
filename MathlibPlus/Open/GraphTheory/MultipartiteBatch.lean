import Mathlib

namespace MathlibPlus.Open.GraphTheory.MultipartiteBatch

/-- A positive weakly descending list whose entries sum to `n`. -/
def IsPartition (n : ℕ) (parts : List ℕ) : Prop :=
  0 < parts.length ∧
    (∀ i : Fin parts.length, 0 < parts.get i) ∧
      (∀ i j : Fin parts.length, i.val < j.val → parts.get j ≤ parts.get i) ∧
        parts.sum = n

/-- Vertices are tagged by their independent part and their position in it. -/
def Vertex (parts : List ℕ) := Σ i : Fin parts.length, Fin (parts.get i)

/-- Adjacency in the complete multipartite graph with part sizes `parts`. -/
def M (parts : List ℕ) (v w : Vertex parts) : Prop := v.1 ≠ w.1

/-- The part fibers of `M` have the prescribed sizes and are independent, with
all cross-part pairs adjacent. -/
def CompleteMultipartiteSpec (n : ℕ) (parts : List ℕ) : Prop :=
  IsPartition n parts →
    (∀ i : Fin parts.length,
      Nonempty ({v : Vertex parts // v.1 = i} ≃ Fin (parts.get i))) ∧
      (∀ v w : Vertex parts, M parts v w ↔ v.1 ≠ w.1)

/-- Claim 23388: `M_parts` is the complete multipartite graph with the part
sizes listed by the partition `parts`. -/
def claim23388 : Prop :=
  ∀ (n : ℕ) (parts : List ℕ), IsPartition n parts → CompleteMultipartiteSpec n parts

def IsSmallestPart (parts : List ℕ) (s : ℕ) : Prop :=
  s ∈ parts ∧ ∀ i : Fin parts.length, s ≤ parts.get i

/-- Removing one occurrence of a smallest part, and reducing it when it is
larger than one. -/
def ReplaceSmallest (s : ℕ) (parts newParts : List ℕ) : Prop :=
  (s = 1 ∧ newParts.Perm (parts.erase 1)) ∨
    (1 < s ∧ newParts.Perm (parts.erase s ++ [s - 1]))

def DeletedVertex (parts : List ℕ) (v : Vertex parts) := {w : Vertex parts // w ≠ v}

/-- Isomorphism of the concrete deleted multipartite relation with another
concrete multipartite relation. -/
def DeletedMultipartiteIso (parts newParts : List ℕ) (v : Vertex parts) : Prop :=
  ∃ e : DeletedVertex parts v ≃ Vertex newParts,
    ∀ x y : DeletedVertex parts v,
      x.1.1 ≠ y.1.1 ↔ (e x).1 ≠ (e y).1

/-- Claim 23389: deleting a vertex in a smallest part performs the stated
one-occurrence partition move and yields the corresponding multipartite graph. -/
def claim23389 : Prop :=
  ∀ (n : ℕ) (parts : List ℕ) (s : ℕ),
    IsPartition n parts →
      IsSmallestPart parts s →
        ∀ (i : Fin parts.length),
          parts.get i = s →
            ∀ (p : Fin (parts.get i)),
              ∃ newParts : List ℕ,
                IsPartition (n - 1) newParts ∧
                  ReplaceSmallest s parts newParts ∧
                    DeletedMultipartiteIso parts newParts ⟨i, p⟩

def MultipartiteParent (remainder parent : List ℕ) : Prop :=
  ∃ (i : Fin parent.length) (p : Fin (parent.get i)),
    DeletedMultipartiteIso parent remainder ⟨i, p⟩

/-- The reverse moves are incrementing one existing part or appending a
singleton part. -/
def ReversePartitionMove (remainder parent : List ℕ) : Prop :=
  (∃ s : ℕ, s ∈ remainder ∧
    parent.Perm (remainder.erase s ++ [s + 1])) ∨
    parent.Perm (remainder ++ [1])

/-- Claim 23390: all complete multipartite parents arise by reversing one
smallest-part deletion. -/
def claim23390 : Prop :=
  ∀ (n : ℕ) (remainder parent : List ℕ),
    IsPartition n remainder →
      IsPartition (n + 1) parent →
        MultipartiteParent remainder parent → ReversePartitionMove remainder parent

def SmallestDeletion (original remainder : List ℕ) : Prop :=
  ∃ s : ℕ, IsSmallestPart original s ∧ ReplaceSmallest s original remainder

/-- Lexicographic order on the finite lists used for fixed-part-count
comparisons. -/
def LexLE : List ℕ → List ℕ → Prop
  | [], [] => True
  | [], _ :: _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ LexLE xs ys)

/-- Claim 23392: in the fixed-part-count parent branch, the original
partition is the unique lexicographically least parent. -/
def claim23392 : Prop :=
  ∀ (n : ℕ) (original remainder : List ℕ),
    IsPartition n original →
      IsPartition (n - 1) remainder →
        SmallestDeletion original remainder →
          ∀ parent : List ℕ,
            IsPartition n parent →
              MultipartiteParent remainder parent →
                parent.length = original.length →
                  LexLE original parent ∧ (LexLE parent original → parent = original)

end MathlibPlus.Open.GraphTheory.MultipartiteBatch
