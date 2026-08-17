import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1171SylowCentralOrbitClaims

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41589Repair

noncomputable section

abbrev Perm (Ω : Type*) := Equiv.Perm Ω
abbrev ElementaryAbelian (p n : ℕ) := Multiplicative (Fin n → ZMod p)

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

def blockActionKernel {Ω : Type*}
    (K P : Subgroup (Perm Ω)) (blocks : Set (Set Ω)) : Prop :=
  K ≤ P ∧
    (∀ k : K, ∀ B : Set Ω, B ∈ blocks →
      (k : Perm Ω) '' B = B) ∧
      (∀ g : Perm Ω, g ∈ P →
        (∀ B : Set Ω, B ∈ blocks → g '' B = B) → g ∈ K)

abbrev blockType {Ω : Type*} (blocks : Set (Set Ω)) :=
  {B : Set Ω // B ∈ blocks}

def actualBlockAction {Ω : Type*}
    (H : Subgroup (Perm Ω)) (blocks : Set (Set Ω))
    (ρ : H →* Perm (blockType blocks)) : Prop :=
  ∀ h : H, ∀ B : blockType blocks,
    ((ρ h) B).1 = (h : Perm Ω) '' B.1

def inducedQuotientRegular {Ω : Type*}
    (H K : Subgroup (Perm Ω)) (blocks : Set (Set Ω))
    (ρ : H →* Perm (blockType blocks)) : Prop :=
  actualBlockAction H blocks ρ ∧
    ρ.ker = K.comap H.subtype ∧
      ∀ B C : blockType blocks,
        ∃! q : ρ.range, (q : Perm (blockType blocks)) B = C

def hasElementaryAbelianType {G : Type*} [Group G]
    (H : Subgroup G) (p n : ℕ) : Prop :=
  Nonempty (H ≃* ElementaryAbelian p n)

/-- The literal quotient carrier is formed only after normality has been
encoded as an existential property of the actual preimage of D. -/
def quotientElementaryAbelian {G : Type*} [Group G]
    (H D : Subgroup G) (p n : ℕ) : Prop :=
  ∃ hD : (D.comap H.subtype).Normal,
    let _ : (D.comap H.subtype).Normal := hD
    Nonempty ((H ⧸ D.comap H.subtype) ≃* ElementaryAbelian p n)

/-- Claim 41589: after quotienting by the common central line, the literal
quotient copies have rank n-1, while their induced images on the D-orbit
blocks are regular. -/
def claim41589 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] (p n : ℕ)
    (X P R T Tx D K : Subgroup (Perm Ω))
    (x : Perm Ω) (blocks : Set (Set Ω)),
    Nat.Prime p → 1 ≤ n →
      MathlibPlus.Open.ResearchFormalization.R1171.finiteRegularAbelianPGroup p R →
        MathlibPlus.Open.ResearchFormalization.R1171.finiteRegularAbelianPGroup p T →
          X = MathlibPlus.Open.ResearchFormalization.R1171.generatedPair R T →
            x ∈ X →
              MathlibPlus.Open.ResearchFormalization.R1171.sylowPSubgroup p X P →
                R ≤ P →
                  conjugationMembership x T Tx →
                    Tx ≤ P →
                      hasElementaryAbelianType R p n →
                        hasElementaryAbelianType T p n →
                          D ≤ MathlibPlus.Open.ResearchFormalization.R1171.ambientCenter P →
                            Nat.card D = p →
                              D ≤ R → D ≤ Tx →
                                blocks = MathlibPlus.Open.ResearchFormalization.R1171.orbitPartition D ∧
                                  MathlibPlus.Open.ResearchFormalization.R1171.permutesPartition
                                    (P : Set (Perm Ω)) blocks →
                                    blockActionKernel K P blocks →
      R ⊓ K = D ∧ Tx ⊓ K = D ∧
        quotientElementaryAbelian R D p (n - 1) ∧
          quotientElementaryAbelian Tx D p (n - 1) ∧
            (∃ ρR : R →* Perm (blockType blocks),
              inducedQuotientRegular R K blocks ρR) ∧
              (∃ ρTx : Tx →* Perm (blockType blocks),
                inducedQuotientRegular Tx K blocks ρTx)

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41589Repair
