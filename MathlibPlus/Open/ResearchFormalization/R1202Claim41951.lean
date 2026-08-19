import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1202Claim32186

namespace MathlibPlus.Open.ResearchFormalization.R1202Claim41951

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchR1267

/-- A regular permutation copy of the finite group `G`. -/
def regularPermutationCopy
    {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω]
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  regularPermutationSubgroup R ∧ Nonempty (R ≃* G)

def uniqueSylowSubgroup
    {p : ℕ} {R : Type*} [Group R]
    (P : Sylow p R) : Prop :=
  ∀ Q : Sylow p R, Q.toSubgroup = P.toSubgroup

def characteristicWithinCopy
    {p : ℕ} {R : Type*} [Group R]
    (P : Sylow p R) : Prop :=
  ∀ φ : R ≃* R,
    Subgroup.map φ.toMonoidHom P.toSubgroup = P.toSubgroup

/-- Claim 41951: under the large-prime regular-copy hypotheses, the Sylow
`p`-subgroup count divides `m` and is one modulo `p`; the resulting unique
Sylow subgroups in both regular copies have order `p^a` and are characteristic
there. -/
def claim41951 : Prop :=
  ∀ (p a m : ℕ),
    Nat.Prime p →
    1 ≤ a →
    m < p →
    ¬ p ∣ m →
    ∀ {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω],
      Fintype.card G = m * p ^ a →
      Fintype.card Ω = m * p ^ a →
      ∀ R T : Subgroup (Equiv.Perm Ω),
        regularPermutationCopy (G := G) R →
        regularPermutationCopy (G := G) T →
        Nat.card (Sylow p G) ∣ m ∧
          Nat.ModEq p (Nat.card (Sylow p G)) 1 ∧
          Nat.card (Sylow p G) = 1 ∧
          ∃ P : Sylow p R, ∃ Q : Sylow p T,
            uniqueSylowSubgroup P ∧
              uniqueSylowSubgroup Q ∧
              Nat.card P.toSubgroup = p ^ a ∧
              Nat.card Q.toSubgroup = p ^ a ∧
              characteristicWithinCopy P ∧
              characteristicWithinCopy Q

end

end MathlibPlus.Open.ResearchFormalization.R1202Claim41951
