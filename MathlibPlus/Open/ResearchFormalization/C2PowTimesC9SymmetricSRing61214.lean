import MathlibPlus.Open.Cayley.C2PowTimesC9

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.C2PowTimesC9SymmetricSRing61214

noncomputable section

abbrev H61214 := MathlibPlus.Open.Cayley.C2PowTimesC9 2
abbrev SRingPartition61214 := Finset (Finset H61214)

/-- The integral group-ring structure constant of two finite subsets. -/
def groupRingCoefficient61214
    (A B : Finset H61214) (x : H61214) : ℕ :=
  (A.product B).filter (fun p : H61214 × H61214 => p.1 + p.2 = x) |>.card

/-- A symmetric S-ring partition over the exact additive carrier
`C₂² × C₉`.  Every basic set is pointwise inverse-invariant, and the last
clause is the integral group-ring structure-constant condition. -/
def isSymmetricSRing61214 (P : SRingPartition61214) : Prop :=
  (∀ A ∈ P, A.Nonempty) ∧
    (∀ A ∈ P, ∀ B ∈ P, A = B ∨ Disjoint A B) ∧
    P.biUnion (fun A => A) = Finset.univ ∧
    ({0} : Finset H61214) ∈ P ∧
    (∀ A ∈ P, A.image (fun x => -x) = A) ∧
    (∀ A ∈ P, ∀ B ∈ P, ∀ C ∈ P,
      ∀ x ∈ C, ∀ y ∈ C,
        groupRingCoefficient61214 A B x = groupRingCoefficient61214 A B y)

def subgroupFinset61214 (K : AddSubgroup H61214) : Finset H61214 :=
  K.carrier.toFinset

/-- Visibility of a subgroup in an S-ring partition. -/
def visibleSubgroup61214
    (P : SRingPartition61214) (K : AddSubgroup H61214) : Prop :=
  ∀ A ∈ P,
    A ⊆ subgroupFinset61214 K ∨ Disjoint A (subgroupFinset61214 K)

/-- The exact factor-S-ring condition on a subgroup carrier. -/
def isFactorSRing61214
    (K : AddSubgroup H61214) (P : SRingPartition61214) : Prop :=
  (∀ A ∈ P, A.Nonempty ∧ A ⊆ subgroupFinset61214 K) ∧
    (∀ A ∈ P, ∀ B ∈ P, A = B ∨ Disjoint A B) ∧
    P.biUnion (fun A => A) = subgroupFinset61214 K ∧
    ({0} : Finset H61214) ∈ P ∧
    (∀ A ∈ P, A.image (fun x => -x) = A) ∧
    (∀ A ∈ P, ∀ B ∈ P, ∀ C ∈ P,
      ∀ x ∈ C, ∀ y ∈ C,
        groupRingCoefficient61214 A B x = groupRingCoefficient61214 A B y)

/-- Product of two factor basic sets under the additive direct-product map. -/
def factorProduct61214 (A B : Finset H61214) : Finset H61214 :=
  A.biUnion (fun a => B.image (fun b => a + b))

/-- A visible nontrivial tensor decomposition with factor S-rings. -/
def tensorWitness61214 (P : SRingPartition61214) : Prop :=
  ∃ A B : AddSubgroup H61214,
    A ≠ ⊥ ∧ B ≠ ⊥ ∧ A ⊔ B = ⊤ ∧ Disjoint A B ∧
      visibleSubgroup61214 P A ∧ visibleSubgroup61214 P B ∧
      ∃ PA PB : SRingPartition61214,
        isFactorSRing61214 A PA ∧ isFactorSRing61214 B PB ∧
          ∀ X ∈ P, ∃ XA ∈ PA, ∃ XB ∈ PB,
            X = factorProduct61214 XA XB

/-- Periodicity of a basic set by a subgroup. -/
def periodicBy61214
    (X : Finset H61214) (L : AddSubgroup H61214) : Prop :=
  ∀ x ∈ X, ∀ l : H61214, l ∈ L → x + l ∈ X

/-- A visible nontrivial generalized-wreath witness. -/
def generalizedWreathWitness61214 (P : SRingPartition61214) : Prop :=
  ∃ L U : AddSubgroup H61214,
    ⊥ < L ∧ L ≤ U ∧ U < ⊤ ∧
      visibleSubgroup61214 P L ∧ visibleSubgroup61214 P U ∧
        ∀ X ∈ P,
          ¬ X ⊆ subgroupFinset61214 U → periodicBy61214 X L

/-- The rank-two partition. -/
def rankTwoPartition61214 : SRingPartition61214 :=
  {({0} : Finset H61214), Finset.univ.erase 0}

def rankTwo61214 (P : SRingPartition61214) : Prop :=
  P = rankTwoPartition61214

abbrev PermH61214 := Equiv.Perm H61214

def additivePermutation61214 (f : PermH61214) : Prop :=
  ∀ x y : H61214, f (x + y) = f x + f y

/-- The subgroups of the full permutation group whose elements are exactly
additive automorphisms of `H`; this is the concrete `Aut(H)` carrier. -/
def automorphismSubgroups61214 : Set (Subgroup PermH61214) :=
  {K | ∀ f : PermH61214, f ∈ K → additivePermutation61214 f}

def orbitAfterInversion61214
    (K : Subgroup PermH61214) (x : H61214) : Finset H61214 :=
  Finset.univ.filter (fun y =>
    ∃ f : PermH61214, f ∈ K ∧
      (y = f x ∨ y = -(f x)))

def cyclotomicPartition61214
    (K : Subgroup PermH61214) : SRingPartition61214 :=
  Finset.univ.image (orbitAfterInversion61214 K)

/-- A symmetric cyclotomic partition is an orbit partition of a subgroup of
`Aut(H)` after adjoining inversion. -/
def cyclotomic61214 (P : SRingPartition61214) : Prop :=
  ∃ K : Subgroup PermH61214,
    K ∈ automorphismSubgroups61214 ∧
      P = cyclotomicPartition61214 K

def partitionRefines61214
    (P Q : SRingPartition61214) : Prop :=
  ∀ A ∈ P, ∃ B ∈ Q, A ⊆ B

def relationComplement61214 (A : Finset H61214) : Finset H61214 :=
  (Finset.univ.erase 0).filter (fun x => x ∉ A)

/-- The three-colour initial partition `{0}`, `A`, and its nonidentity
complement used to generate a one-relation S-ring. -/
def relationSeed61214 (A : Finset H61214) : SRingPartition61214 :=
  {({0} : Finset H61214), A, relationComplement61214 A}

def identityFreeInverseClosed61214 (A : Finset H61214) : Prop :=
  0 ∉ A ∧ A.image (fun x => -x) = A

/-- Least symmetric S-ring refining the initial one-relation colouring. -/
def generatedByOneRelation61214
    (A : Finset H61214) (P : SRingPartition61214) : Prop :=
  isSymmetricSRing61214 P ∧
    partitionRefines61214 P (relationSeed61214 A) ∧
      ∀ Q : SRingPartition61214,
        isSymmetricSRing61214 Q →
          partitionRefines61214 Q (relationSeed61214 A) →
            partitionRefines61214 Q P

def oneRelationRings61214 : Set SRingPartition61214 :=
  {P | ∃ A : Finset H61214,
    identityFreeInverseClosed61214 A ∧ generatedByOneRelation61214 A P}

/-- The least symmetric S-ring common refinement of a finite family of
one-relation rings. -/
def joinGeneratedByOneRelations61214
    (P : SRingPartition61214) : Prop :=
  isSymmetricSRing61214 P ∧
    ∃ F : Finset SRingPartition61214,
      F.Nonempty ∧
        (∀ Q ∈ F, Q ∈ oneRelationRings61214) ∧
        (∀ Q ∈ F, partitionRefines61214 P Q) ∧
          ∀ R : SRingPartition61214,
            isSymmetricSRing61214 R →
              (∀ Q ∈ F, partitionRefines61214 R Q) →
                partitionRefines61214 R P

def allSymmetricRings61214 : Set SRingPartition61214 :=
  {P | isSymmetricSRing61214 P}

/-- Claim 61214: the complete 279-ring symmetric S-ring classification of
`C₂² × C₉`, including the category counts, exact overlap profile, and the
272 one-relation generators and their 279-element join closure. -/
def claim61214_exhaustiveSymmetricSRingClassification : Prop :=
  Set.ncard allSymmetricRings61214 = 279 ∧
    (∀ P : SRingPartition61214, isSymmetricSRing61214 P →
      rankTwo61214 P ∨ cyclotomic61214 P ∨
        tensorWitness61214 P ∨ generalizedWreathWitness61214 P) ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ rankTwo61214 P} = 1 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ cyclotomic61214 P} = 12 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ tensorWitness61214 P} = 69 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ generalizedWreathWitness61214 P} = 266 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧
        (rankTwo61214 P ∨ cyclotomic61214 P ∨
          tensorWitness61214 P ∨ generalizedWreathWitness61214 P)} = 279 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ rankTwo61214 P ∧
        ¬ cyclotomic61214 P ∧ ¬ tensorWitness61214 P ∧
        ¬ generalizedWreathWitness61214 P} = 1 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ ¬ rankTwo61214 P ∧
        cyclotomic61214 P ∧
        ¬ tensorWitness61214 P ∧ ¬ generalizedWreathWitness61214 P} = 2 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ ¬ rankTwo61214 P ∧
        cyclotomic61214 P ∧
        tensorWitness61214 P ∧ ¬ generalizedWreathWitness61214 P} = 2 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ ¬ rankTwo61214 P ∧
        cyclotomic61214 P ∧
        tensorWitness61214 P ∧ generalizedWreathWitness61214 P} = 8 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ ¬ rankTwo61214 P ∧
        ¬ cyclotomic61214 P ∧
        tensorWitness61214 P ∧ ¬ generalizedWreathWitness61214 P} = 8 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ ¬ rankTwo61214 P ∧
        ¬ cyclotomic61214 P ∧
        tensorWitness61214 P ∧ generalizedWreathWitness61214 P} = 51 ∧
    Set.ncard {P : SRingPartition61214 |
      isSymmetricSRing61214 P ∧ ¬ rankTwo61214 P ∧
        ¬ cyclotomic61214 P ∧ ¬ tensorWitness61214 P ∧
        generalizedWreathWitness61214 P} = 207 ∧
    Set.ncard (automorphismSubgroups61214) = 36 ∧
    Set.ncard {A : Finset H61214 |
      identityFreeInverseClosed61214 A} = 2 ^ 19 ∧
    (∀ A : Finset H61214,
      identityFreeInverseClosed61214 A →
        ∃! P : SRingPartition61214, generatedByOneRelation61214 A P) ∧
    Set.ncard oneRelationRings61214 = 272 ∧
    Set.ncard {P : SRingPartition61214 |
      joinGeneratedByOneRelations61214 P} = 279 ∧
    {P : SRingPartition61214 | joinGeneratedByOneRelations61214 P} =
      allSymmetricRings61214

end

end MathlibPlus.Open.ResearchFormalization.C2PowTimesC9SymmetricSRing61214
