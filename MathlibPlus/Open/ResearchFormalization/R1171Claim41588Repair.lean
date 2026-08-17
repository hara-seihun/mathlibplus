import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1171SylowCentralOrbitClaims

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41588Repair

noncomputable section

abbrev Perm (Ω : Type*) := Equiv.Perm Ω

/-- Regularity of a displayed permutation copy. -/
def regularPermutationCopy {Ω : Type*}
    (H : Subgroup (Perm Ω)) : Prop :=
  ∀ a b : Ω, ∃! h : H, (h : Perm Ω) a = b

def abelianPermutationCopy {Ω : Type*}
    (H : Subgroup (Perm Ω)) : Prop :=
  ∀ h k : H, (h : Perm Ω) * (k : Perm Ω) =
    (k : Perm Ω) * (h : Perm Ω)

def conjugationMembership {Ω : Type*}
    (x : Perm Ω) (H S : Subgroup (Perm Ω)) : Prop :=
  ∀ g : Perm Ω, g ∈ S ↔ ∃ h : H, g = x⁻¹ * (h : Perm Ω) * x

/-- The kernel of the setwise action on a specified block system. -/
def blockActionKernel {Ω : Type*}
    (K P : Subgroup (Perm Ω)) (blocks : Set (Set Ω)) : Prop :=
  K ≤ P ∧
    (∀ k : K, ∀ B : Set Ω, B ∈ blocks →
      (k : Perm Ω) '' B = B) ∧
      (∀ g : Perm Ω, g ∈ P →
        (∀ B : Set Ω, B ∈ blocks → g '' B = B) → g ∈ K)

abbrev blockType {Ω : Type*} (blocks : Set (Set Ω)) :=
  {B : Set Ω // B ∈ blocks}

/-- A block action homomorphism is required to be the actual action on the
sets in the block system, rather than an arbitrary permutation certificate. -/
def actualBlockAction {Ω : Type*}
    (H : Subgroup (Perm Ω)) (blocks : Set (Set Ω))
    (ρ : H →* Perm (blockType blocks)) : Prop :=
  ∀ h : H, ∀ B : blockType blocks,
    ((ρ h) B).1 = (h : Perm Ω) '' B.1

/-- Regularity is stated on the induced image, so uniqueness is modulo the
block-action kernel rather than uniqueness of an element of the original copy. -/
def inducedQuotientRegular {Ω : Type*}
    (H K : Subgroup (Perm Ω)) (blocks : Set (Set Ω))
    (ρ : H →* Perm (blockType blocks)) : Prop :=
  actualBlockAction H blocks ρ ∧
    ρ.ker = K.comap H.subtype ∧
      ∀ B C : blockType blocks,
        ∃! q : ρ.range, (q : Perm (blockType blocks)) B = C

/-- Claim 41588: the block kernel meets each regular copy in the common
central line, and the two induced quotient images act regularly on the actual
D-orbit block set. -/
def claim41588 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] (p : ℕ)
    (X P R T Tx D K : Subgroup (Perm Ω))
    (x : Perm Ω) (blocks : Set (Set Ω)),
    Nat.Prime p →
      MathlibPlus.Open.ResearchFormalization.R1171.finiteRegularAbelianPGroup p R →
        MathlibPlus.Open.ResearchFormalization.R1171.finiteRegularAbelianPGroup p T →
          X = MathlibPlus.Open.ResearchFormalization.R1171.generatedPair R T →
            x ∈ X →
              MathlibPlus.Open.ResearchFormalization.R1171.sylowPSubgroup p X P →
                R ≤ P →
                  conjugationMembership x T Tx →
                    Tx ≤ P →
                      D ≤ MathlibPlus.Open.ResearchFormalization.R1171.ambientCenter P →
                        Nat.card D = p →
                          D ≤ R → D ≤ Tx →
                            blocks = MathlibPlus.Open.ResearchFormalization.R1171.orbitPartition D ∧
                              MathlibPlus.Open.ResearchFormalization.R1171.permutesPartition
                                (P : Set (Perm Ω)) blocks →
                                blockActionKernel K P blocks →
      R ⊓ K = D ∧ Tx ⊓ K = D ∧
        (∃ ρR : R →* Perm (blockType blocks),
          inducedQuotientRegular R K blocks ρR) ∧
        (∃ ρTx : Tx →* Perm (blockType blocks),
          inducedQuotientRegular Tx K blocks ρTx)

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41588Repair
