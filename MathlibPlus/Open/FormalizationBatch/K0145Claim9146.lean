import MathlibPlus.Open.FormalizationBatchK0145

namespace MathlibPlus.Open.FormalizationBatch.K0145Claim9146

open MathlibPlus.Open.FormalizationBatchK0145
open Classical

noncomputable section

abbrev Vertex9146 := Vertex24

/-- The fixed representative used by the finite catalogue count. -/
def representative9146 (C : GraphClass24) : SimpleGraph Vertex9146 :=
  Quotient.out C

def admissibleClasses9146 : Finset GraphClass24 :=
  Finset.univ.filter (fun C => ClassHasR45 C)

def fixedPointCount9146 (σ : Equiv.Perm Vertex9146) : ℕ :=
  (Finset.univ.filter (fun x => σ x = x)).card

def hasPrimeCycleType9146
    (G : SimpleGraph Vertex9146) (p cycles fixed : ℕ)
    (σ : GraphAut G) : Prop :=
  Nat.Prime p ∧
    orderOf σ.1 = p ∧
    σ.1.cycleType.count p = cycles ∧
    fixedPointCount9146 σ.1 = fixed

def automorphismsOfType9146
    (C : GraphClass24) (p cycles fixed : ℕ) :
    Finset (GraphAut (representative9146 C)) :=
  Finset.univ.filter
    (hasPrimeCycleType9146 (representative9146 C) p cycles fixed)

def graphAndElementCounts9146
    (p cycles fixed : ℕ) : ℕ × ℕ :=
  ((admissibleClasses9146.filter
      (fun C => ∃ σ,
        hasPrimeCycleType9146 (representative9146 C) p cycles fixed σ)).card,
    admissibleClasses9146.sum
      (fun C => (automorphismsOfType9146 C p cycles fixed).card))

/-- The element column of the complete one-representative-per-isomorphism-class
R(4,5) catalogue sums to 12634 over all prime-order cycle types. -/
def totalPrimeOrderAutomorphisms_claim9146 : Prop :=
  (graphAndElementCounts9146 2 8 8).2 +
    (graphAndElementCounts9146 2 9 6).2 +
    (graphAndElementCounts9146 2 10 4).2 +
    (graphAndElementCounts9146 2 11 2).2 +
    (graphAndElementCounts9146 2 12 0).2 +
    (graphAndElementCounts9146 3 7 3).2 +
    (graphAndElementCounts9146 3 8 0).2 = 12634

end

end MathlibPlus.Open.FormalizationBatch.K0145Claim9146
