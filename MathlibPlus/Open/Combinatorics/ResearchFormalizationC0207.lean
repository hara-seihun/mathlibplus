import Mathlib

namespace MathlibPlus.Open.Combinatorics.ResearchFormalizationC0207

/-- Delete the zero parts from the displayed row lists. -/
def deleteZeroParts (parts : List ℕ) : List ℕ :=
  parts.filter (· ≠ 0)

def repeated (n v : ℕ) : List ℕ := List.replicate n v

def isPartition (parts : List ℕ) : Prop :=
  parts.Pairwise (· ≥ ·) ∧ ∀ n ∈ parts, 0 < n

def theta (C r p : ℕ) : List ℕ :=
  deleteZeroParts (repeated p (C + 1) ++ repeated (r - p) C)

def lambdaNearRectangle (C r p : ℕ) : List ℕ :=
  deleteZeroParts (repeated p (C + 1) ++ repeated (r - p) (C - 1))

def rhoNearRectangle (C r : ℕ) : List ℕ :=
  deleteZeroParts (repeated r (C + 1))

def muNearRectangle (C r p : ℕ) : List ℕ :=
  deleteZeroParts (repeated p (C + 2) ++ repeated (r - p - 1) C)

def sigmaNearRectangle (C r : ℕ) : List ℕ :=
  deleteZeroParts (repeated (r + 1) C)

/-- The five near-rectangle partitions in Claim 3028. -/
def claim3028 : Prop :=
  ∀ (C r p : ℕ),
    1 ≤ C → 2 ≤ r → 1 ≤ p → p < r →
      isPartition (theta C r p) ∧
      isPartition (lambdaNearRectangle C r p) ∧
      isPartition (rhoNearRectangle C r) ∧
      isPartition (muNearRectangle C r p) ∧
      isPartition (sigmaNearRectangle C r)

end MathlibPlus.Open.Combinatorics.ResearchFormalizationC0207
