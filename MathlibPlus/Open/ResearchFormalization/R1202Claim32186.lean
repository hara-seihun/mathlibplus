import MathlibPlus.Open.ResearchFormalization.BatchR1267

namespace MathlibPlus.Open.ResearchFormalization.R1202

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchR1267

abbrev CpPowerS3 (p r : ℕ) :=
  Multiplicative (Fin r → ZMod p) × Equiv.Perm (Fin 3)

def conjugateSubgroup32186 {Ω : Type*}
    (x : Equiv.Perm Ω) (Q : Subgroup (Equiv.Perm Ω)) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.map (MulAut.conj x.symm).toMonoidHom Q

def ambientSylow32186 {p : ℕ} {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) (P : Sylow p R) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.map R.subtype P.toSubgroup

def uniqueSylowP32186 {p : ℕ} {Ω : Type*}
    [Fintype Ω] [Fact p.Prime]
    (R : Subgroup (Equiv.Perm Ω)) (P : Sylow p R) : Prop :=
  ∀ Q : Sylow p R, Q.1 = P.1

def regularCopyOfCpPowerS3_32186
    (p r : ℕ) {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  regularPermutationSubgroup R ∧
    Nonempty (R ≃* CpPowerS3 p r)

/-- Claim 32186: for `p≥7`, characteristic Sylow-`p` subgroups of two
regular copies of `C_p^r × S₃` can be aligned inside their generated group,
with the common six-block orbit partition and its exact block sizes. -/
def claim32186 : Prop :=
  ∀ (p r : ℕ), (hp : Nat.Prime p) → 7 ≤ p → 1 ≤ r →
    ∀ (Ω : Type*) [Fintype Ω],
      Fintype.card Ω = 6 * p ^ r →
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      ∀ R T : Subgroup (Equiv.Perm Ω),
        regularCopyOfCpPowerS3_32186 p r R →
        regularCopyOfCpPowerS3_32186 p r T →
        let X := Subgroup.closure
          ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω)))
        ∃ P : Sylow p R, ∃ Q : Sylow p T,
          uniqueSylowP32186 R P ∧
          uniqueSylowP32186 T Q ∧
          ∃ x : X,
            let Qx := conjugateSubgroup32186
              (x : Equiv.Perm Ω) (ambientSylow32186 T Q)
            orbitPartition (ambientSylow32186 R P) = orbitPartition Qx ∧
            Nat.card (orbitPartition (ambientSylow32186 R P)) = 6 ∧
            (∀ B : Set Ω, B ∈ orbitPartition (ambientSylow32186 R P) →
              Set.ncard B = p ^ r)

end
end MathlibPlus.Open.ResearchFormalization.R1202
