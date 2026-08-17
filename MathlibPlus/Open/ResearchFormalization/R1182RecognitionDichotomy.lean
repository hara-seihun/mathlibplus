import MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722
import MathlibPlus.Open.ResearchFormalization.R1182.Claim41710
import MathlibPlus.Open.ResearchFormalization.Claim31958

namespace MathlibPlus.Open.ResearchFormalization.R1182Repair

noncomputable section

open Classical

open MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

/-- The affine block/chart hypothesis used by the normalized prime-block
lift theorem, on the concrete `C₁₃ × Q₁₂` recognition carrier. -/
def affineChartHypotheses41723 (f : Equiv.Perm G156) : Prop :=
  ∃ (orientation : Bool)
    (lam : Q12 → (ZMod 13)ˣ) (tau : Q12 → ZMod 13),
    MathlibPlus.Open.ResearchFormalization.R1182.Claim41710.normalizedAffineFunctions
      lam tau ∧
      ∀ z : MathlibPlus.Open.ResearchFormalization.R1182.Claim41710.PrimeBlock 13,
        f z =
          MathlibPlus.Open.ResearchFormalization.R1182.Claim41710.affineLiftMap
            13 orientation lam tau z

def affineLiftTheoremHypotheses41723 (f : Equiv.Perm G156) : Prop :=
  commonBlockPreserving f ∧ affineChartHypotheses41723 f

/-- Claim 41723: the exact disconnected recognition graph has the connected
nontrivial quotient and exceptional cross-class lifts, while its full
automorphism group contains both the partition-breaking switch and the
block-preserving nonlinear fibre map; the latter does not satisfy the affine
block/chart hypotheses. -/
def characteristicC13RecognitionFailure_claim41723 : Prop :=
  claim41718 ∧
    ¬ connectedRelation recognitionAdj ∧
      claim41720 ∧
        claim41721 ∧
          claim41722 ∧
            ¬ affineLiftTheoremHypotheses41723 nu

def conjugatedCopy41724 {V : Type*}
    (g : Equiv.Perm V)
    (R R' : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ h : Equiv.Perm V,
    h ∈ R' ↔ g⁻¹ * h * g ∈ R

def transportPermutation41724
    (e : Fin 12 ≃ Q12) (σ : Equiv.Perm (Fin 12)) : Equiv.Perm Q12 :=
  e.symm.trans (σ.trans e)

def transportedSubgroupSet41724
    (e : Fin 12 ≃ Q12)
    (A : Subgroup (Equiv.Perm (Fin 12))) : Set (Equiv.Perm Q12) :=
  {g | ∃ a : A, g = transportPermutation41724 e a.1}

def exceptionalQuotientImage41724
    (A : Subgroup (Equiv.Perm (Fin 12))) : Prop :=
  ∃ e : Fin 12 ≃ Q12,
    (transportedSubgroupSet41724 e A =
        (exceptionalAmbient127 : Set (Equiv.Perm Q12)) ∨
      transportedSubgroupSet41724 e A =
        (exceptionalAmbient204 : Set (Equiv.Perm Q12)))

def generatedQuotientImage41724 {R T : Type*}
    [Group R] [Group T]
    (qR : R →* Equiv.Perm (Fin 12))
    (qT : T →* Equiv.Perm (Fin 12)) :
    Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.map qR ⊤ ⊔ Subgroup.map qT ⊤

def commonPQuotientReduction41724 (p : ℕ)
    (S : Set (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p))
    (R T : Subgroup
      (Equiv.Perm (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p))) :
    Prop :=
  ∃ (g h : Equiv.Perm
      (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p))
    (R' T' : Subgroup
      (Equiv.Perm (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p))),
    MathlibPlus.Open.ResearchFormalization.Claim31958.graphAutomorphism
        (MathlibPlus.Open.ResearchFormalization.Claim31958.cayleyGraph S) g ∧
      MathlibPlus.Open.ResearchFormalization.Claim31958.graphAutomorphism
        (MathlibPlus.Open.ResearchFormalization.Claim31958.cayleyGraph S) h ∧
      conjugatedCopy41724 g R R' ∧
        conjugatedCopy41724 h T T' ∧
          MathlibPlus.Open.ResearchFormalization.Claim31958.regularPermutationSubgroup
              (A := MathlibPlus.Open.ResearchFormalization.Claim31958.Q12p p) R' ∧
            MathlibPlus.Open.ResearchFormalization.Claim31958.regularPermutationSubgroup
              (A := MathlibPlus.Open.ResearchFormalization.Claim31958.Q12p p) T' ∧
              MathlibPlus.Open.ResearchFormalization.Claim31958.subgroupGraphAutomorphism
                (MathlibPlus.Open.ResearchFormalization.Claim31958.cayleyGraph S) R' ∧
                MathlibPlus.Open.ResearchFormalization.Claim31958.subgroupGraphAutomorphism
                  (MathlibPlus.Open.ResearchFormalization.Claim31958.cayleyGraph S) T' ∧
                  ∃ blocks : Fin 12 → Set
                    (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p),
                    MathlibPlus.Open.ResearchFormalization.Claim31958.characteristicPrimeBlockSystem
                      p R' blocks ∧
                      MathlibPlus.Open.ResearchFormalization.Claim31958.characteristicPrimeBlockSystem
                        p T' blocks ∧
                        ∃ (qR : R' →* Equiv.Perm (Fin 12))
                          (qT : T' →* Equiv.Perm (Fin 12)),
                          MathlibPlus.Open.ResearchFormalization.Claim31958.blockActionCompatible
                            R' blocks qR ∧
                            MathlibPlus.Open.ResearchFormalization.Claim31958.blockActionCompatible
                              T' blocks qT ∧
                              MathlibPlus.Open.ResearchFormalization.Claim31958.q12RegularOn
                                (Subgroup.map qR ⊤) ∧
                              MathlibPlus.Open.ResearchFormalization.Claim31958.q12RegularOn
                                (Subgroup.map qT ⊤) ∧
                              (exceptionalQuotientImage41724
                                  (generatedQuotientImage41724 qR qT) ∨
                                ∃ parts : Fin 4 → Set (Fin 12),
                                  MathlibPlus.Open.ResearchFormalization.Claim31958.fourTriplePartition
                                    (Subgroup.map qR ⊤)
                                    (Subgroup.map qT ⊤) parts)

/-- Claim 41724: after conjugating the two regular copies to a common
characteristic-prime block system, the quotient pair is exceptional or has a
common normal four-triple partition. -/
def commonPQuotientDichotomy_claim41724 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    (∀ q : ℕ, Nat.Prime q → q % 2 = 1 → q ∣ (12 * p) → q ≤ p) →
      ∀ S : Set
        (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p),
        MathlibPlus.Open.ResearchFormalization.Claim31958.inverseClosed S →
          ∀ R T : Subgroup
            (Equiv.Perm
              (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p)),
            MathlibPlus.Open.ResearchFormalization.Claim31958.regularPermutationSubgroup
                (A := MathlibPlus.Open.ResearchFormalization.Claim31958.Q12p p) R →
              MathlibPlus.Open.ResearchFormalization.Claim31958.regularPermutationSubgroup
                (A := MathlibPlus.Open.ResearchFormalization.Claim31958.Q12p p) T →
                MathlibPlus.Open.ResearchFormalization.Claim31958.subgroupGraphAutomorphism
                  (MathlibPlus.Open.ResearchFormalization.Claim31958.cayleyGraph S) R →
                  MathlibPlus.Open.ResearchFormalization.Claim31958.subgroupGraphAutomorphism
                    (MathlibPlus.Open.ResearchFormalization.Claim31958.cayleyGraph S) T →
                    commonPQuotientReduction41724 p S R T

def normalBranchConclusion41725 (p : ℕ)
    {V : Type*} (R : Subgroup (Equiv.Perm V))
    (blocks : Fin 12 → Set V) (parts : Fin 4 → Set (Fin 12)) : Prop :=
  MathlibPlus.Open.ResearchFormalization.Claim31958.fourBlockPartitionOnVertex
      (MathlibPlus.Open.ResearchFormalization.Claim31958.pullbackBlock blocks parts) ∧
    MathlibPlus.Open.ResearchFormalization.Claim31958.normalBranchHallConclusion
      p R blocks parts

def normalBranchConclusionBoth41725 (p : ℕ)
    {V : Type*} (R T : Subgroup (Equiv.Perm V))
    (blocks : Fin 12 → Set V) (parts : Fin 4 → Set (Fin 12)) : Prop :=
  normalBranchConclusion41725 p R blocks parts ∧
    normalBranchConclusion41725 p T blocks parts

/-- Claim 41725: in the normal quotient branch, the four quotient triples
pull back to common `3p` blocks and each regular copy has its unique
characteristic odd Hall `C₃p` block stabilizer. -/
def normalQuotientBranchGivesFourHallBlocks_claim41725 : Prop :=
  ∀ p : ℕ,
    Nat.Prime p → 3 < p →
      (∀ q : ℕ, Nat.Prime q → q % 2 = 1 → q ∣ (12 * p) → q ≤ p) →
        ∀ S : Set
          (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p),
          MathlibPlus.Open.ResearchFormalization.Claim31958.inverseClosed S →
            ∀ R T : Subgroup
              (Equiv.Perm
                (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p)),
              MathlibPlus.Open.ResearchFormalization.Claim31958.regularPermutationSubgroup
                  (A := MathlibPlus.Open.ResearchFormalization.Claim31958.Q12p p) R →
                MathlibPlus.Open.ResearchFormalization.Claim31958.regularPermutationSubgroup
                  (A := MathlibPlus.Open.ResearchFormalization.Claim31958.Q12p p) T →
                  MathlibPlus.Open.ResearchFormalization.Claim31958.subgroupGraphAutomorphism
                    (MathlibPlus.Open.ResearchFormalization.Claim31958.cayleyGraph S) R →
                    MathlibPlus.Open.ResearchFormalization.Claim31958.subgroupGraphAutomorphism
                      (MathlibPlus.Open.ResearchFormalization.Claim31958.cayleyGraph S) T →
                      ∀ blocks : Fin 12 → Set
                        (MathlibPlus.Open.ResearchFormalization.Claim31958.CayleyVertex p),
                        MathlibPlus.Open.ResearchFormalization.Claim31958.characteristicPrimeBlockSystem
                          p R blocks →
                          MathlibPlus.Open.ResearchFormalization.Claim31958.characteristicPrimeBlockSystem
                            p T blocks →
                            ∀ qR : R →* Equiv.Perm (Fin 12),
                              ∀ qT : T →* Equiv.Perm (Fin 12),
                                MathlibPlus.Open.ResearchFormalization.Claim31958.blockActionCompatible
                                  R blocks qR →
                                  MathlibPlus.Open.ResearchFormalization.Claim31958.blockActionCompatible
                                    T blocks qT →
                                    MathlibPlus.Open.ResearchFormalization.Claim31958.q12RegularOn
                                      (Subgroup.map qR ⊤) →
                                      MathlibPlus.Open.ResearchFormalization.Claim31958.q12RegularOn
                                        (Subgroup.map qT ⊤) →
                                        ∀ parts : Fin 4 → Set (Fin 12),
                                          MathlibPlus.Open.ResearchFormalization.Claim31958.fourTriplePartition
                                            (Subgroup.map qR ⊤)
                                            (Subgroup.map qT ⊤) parts →
                                            normalBranchConclusionBoth41725
                                              p R T blocks parts

end
end MathlibPlus.Open.ResearchFormalization.R1182Repair
