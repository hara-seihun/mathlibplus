import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim10658

noncomputable section

/-- The squarefree positive integers at the retained cutoff. -/
noncomputable def bulkVertexSet : Finset ℕ :=
  (Finset.Icc 1 300000).filter (fun n => Squarefree n)

def mobiusSign (n : ℕ) : ℤ :=
  Int.sign (ArithmeticFunction.moebius n)

/-- An undirected one-prime toggle is represented once with its smaller endpoint
first, and joins opposite Mobius signs. -/
def onePrimeToggleEdge (u v : ℕ) : Prop :=
  u ∈ bulkVertexSet ∧
    v ∈ bulkVertexSet ∧
    u < v ∧
    u ∣ v ∧
    Nat.Prime (v / u) ∧
    mobiusSign u = -mobiusSign v

def onePrimeToggleMatching (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ e ∈ M, onePrimeToggleEdge e.1 e.2) ∧
    (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)

noncomputable def matchedVertices (M : Finset (ℕ × ℕ)) : Finset ℕ :=
  M.biUnion (fun e => ({e.1, e.2} : Finset ℕ))

noncomputable def unmatchedVertices (M : Finset (ℕ × ℕ)) : Finset ℕ :=
  bulkVertexSet \ matchedVertices M

def onePrimeToggleMaximumMatching (M : Finset (ℕ × ℕ)) : Prop :=
  onePrimeToggleMatching M ∧
    ∀ N : Finset (ℕ × ℕ),
      onePrimeToggleMatching N →
        (unmatchedVertices M).card ≤ (unmatchedVertices N).card

noncomputable def bulkColorImbalance : ℕ :=
  Int.natAbs
    (((bulkVertexSet.filter (fun n => mobiusSign n = 1)).card : ℤ) -
      ((bulkVertexSet.filter (fun n => mobiusSign n = -1)).card : ℤ))

/-- Claim 10658: the literal one-prime squarefree-toggle graph has a maximum
matching leaving 50132 vertices unmatched at X=300000, while its two Mobius
color classes differ by only 220. -/
def exactBulkDefect_claim10658 : Prop :=
  ∃ M : Finset (ℕ × ℕ),
    onePrimeToggleMaximumMatching M ∧
      (unmatchedVertices M).card = 50132 ∧
      bulkColorImbalance = 220 ∧
      (50132 : ℚ) / 300000 = 12533 / 75000 ∧
      (12533 : ℚ) / 75000 > 1 / 6 ∧
      (220 : ℚ) / 300000 < 1 / 6 ∧
      (220 : ℕ) < 50132

end

end MathlibPlus.Combinatorics.Claim10658
