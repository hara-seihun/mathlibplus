import MathlibPlus.Open.ResearchFormalization.R1171SylowCentralOrbitClaims

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim31818_31822Repair

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1171

/-- Claim 31818: both regular copies enter one Sylow `p`-subgroup, with the
conjugating element and the conjugated second copy retained. -/
def claim31818_sylowReduction : Prop :=
  ∀ (p : ℕ) (Ω : Type*) [Fintype Ω]
    (R T : Subgroup (Perm Ω)),
    commonSylowHypotheses p R T →
      let X := generatedPair R T
      ∃ (P : Subgroup (Perm Ω)) (x : Perm Ω),
        x ∈ X ∧
          sylowPSubgroup p X P ∧
            R ≤ P ∧
              (∀ t : T, x⁻¹ * (t : Perm Ω) * x ∈ P)

/-- Claim 31820: the center supplied by the common Sylow reduction is
nontrivial and lies in both regular copies, with the second copy conjugated
by the retained element `x`. -/
def claim31820_nontrivialCommonCenter : Prop :=
  ∀ (p : ℕ) (Ω : Type*) [Fintype Ω]
    (R T : Subgroup (Perm Ω))
    (X P : Subgroup (Perm Ω)) (x : Perm Ω),
    commonSylowHypotheses p R T →
      commonSylowData p R T X P x →
        ambientCenter P ≠ ⊥ ∧
          centerContainedInRegularCopies R T P x

/-- Claim 31821: a central order-`p` subgroup is forced into the regular
copy and has semiregular, `p`-point orbits. -/
def claim31821_centralOrderPSemiregular : Prop :=
  ∀ (p : ℕ) (Ω : Type*) [Fintype Ω]
    (R T : Subgroup (Perm Ω))
    (X P : Subgroup (Perm Ω)) (x : Perm Ω)
    (D : Subgroup (Perm Ω)),
    commonSylowHypotheses p R T →
      commonSylowData p R T X P x →
        D ≤ ambientCenter P →
          Nat.card D = p →
            D ≤ R ∧
              ∀ ω : Ω, Set.ncard (orbitSet D ω) = p

/-- Claim 31822: the central prime-orbit partition has `p`-point blocks and
is permuted by `P`, `R`, and the conjugated copy `T^x`. -/
def claim31822_centralPrimeInvariantBlocks : Prop :=
  ∀ (p : ℕ) (Ω : Type*) [Fintype Ω]
    (R T : Subgroup (Perm Ω))
    (X P : Subgroup (Perm Ω)) (x : Perm Ω)
    (D : Subgroup (Perm Ω)),
    commonSylowHypotheses p R T →
      commonSylowData p R T X P x →
        D ≤ ambientCenter P →
          Nat.card D = p →
            (∀ B : Set Ω, B ∈ orbitPartition D → Set.ncard B = p) ∧
              permutesPartition (P : Set (Perm Ω)) (orbitPartition D) ∧
                permutesPartition (R : Set (Perm Ω)) (orbitPartition D) ∧
                  permutesPartition
                    {g : Perm Ω | ∃ t : T,
                      g = x⁻¹ * (t : Perm Ω) * x}
                    (orbitPartition D)

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim31818_31822Repair
