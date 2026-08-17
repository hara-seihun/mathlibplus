import MathlibPlus.Open.Research.CIAtlas

open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0980PartitionSplit27860

noncomputable section

abbrev G72 := MathlibPlus.Open.Research.CIAtlas.C2CubedC9

/-- The exact valency-13 connection-set carrier. -/
def connectionSet13 (S : Finset G72) : Prop :=
  MathlibPlus.Open.Research.CIAtlas.connectionSet72 13 S

/-- A graph automorphism of the ordinary Cayley graph carried by `S`. -/
def graphPermutation (S : Finset G72) :=
  {e : Equiv.Perm G72 //
    ∀ x y,
      MathlibPlus.Open.Research.CIAtlas.graphAdjacent72 S x y ↔
        MathlibPlus.Open.Research.CIAtlas.graphAdjacent72 S (e x) (e y)}

/-- Equality of the natural nine coset labels of two group elements. -/
def sameNaturalBase (x y : G72) : Prop :=
  x.2.2.2 = y.2.2.2

def preservesNaturalPartition (S : Finset G72)
    (φ : graphPermutation S) : Prop :=
  ∀ x y, sameNaturalBase x y ↔ sameNaturalBase (φ.1 x) (φ.1 y)

def partitionBreaking (S : Finset G72) : Prop :=
  ∃ φ : graphPermutation S, ¬ preservesNaturalPartition S φ

def partitionPreserving (S : Finset G72) : Prop :=
  ∀ φ : graphPermutation S, preservesNaturalPartition S φ

/-- Normality of the regular translation presentation inside the graph
automorphism group. -/
def normalPresentation (S : Finset G72) : Prop :=
  ∀ φ : graphPermutation S, ∀ g : G72, ∃ h : G72, ∀ x : G72,
    φ.1 (g + φ.1.symm x) = h + x

abbrev Presentation13 := {S : Finset G72 // connectionSet13 S}

def presentationCensus (n : ℕ) (P : Presentation13 → Prop) : Prop :=
  ∃ representatives : Fin n → Presentation13,
    (∀ i, P (representatives i)) ∧
      (∀ i j, i ≠ j →
        ¬ MathlibPlus.Open.Research.CIAtlas.autEquivalent72
            (representatives i).1 (representatives j).1) ∧
      ∀ S : Presentation13, P S →
        ∃ i,
          MathlibPlus.Open.Research.CIAtlas.autEquivalent72
            S.1 (representatives i).1

/-- Claim 27860: the exact valency-13 nonnormal presentation types split
into the 2,774 partition breakers and 1,610 partition preservers, and every
breaker is nonnormal. -/
def claim27860 : Prop :=
  presentationCensus 2774
      (fun S => partitionBreaking S.1 ∧ ¬ normalPresentation S.1) ∧
    presentationCensus 1610
      (fun S => partitionPreserving S.1 ∧ ¬ normalPresentation S.1) ∧
    2774 + 1610 = 4384 ∧
    (∀ S : Presentation13,
      partitionBreaking S.1 → ¬ normalPresentation S.1)

end

end MathlibPlus.Open.ResearchFormalization.R0980PartitionSplit27860
