import Mathlib
import MathlibPlus.GroupTheory.Claim41584RegularPermutationCentralizer

namespace MathlibPlus.Open.ResearchFormalization.R1171

noncomputable section

abbrev Perm (Ω : Type*) := Equiv.Perm Ω

def displayedRegularCopy {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Perm Ω)) : Prop :=
  ∃ e : R ≃ Ω,
    (R : Set (Perm Ω)) =
      Set.range (fun g : R =>
        (e.symm.trans (Equiv.mulLeft g)).trans e)

def abelianPermutationCopy {Ω : Type*}
    (R : Subgroup (Perm Ω)) : Prop :=
  ∀ r s : R,
    (r : Perm Ω) * (s : Perm Ω) = (s : Perm Ω) * (r : Perm Ω)

def permutationPGroup {Ω : Type*}
    (p : ℕ) (R : Subgroup (Perm Ω)) : Prop :=
  ∀ r : R, ∃ k : ℕ, orderOf (r : Perm Ω) = p ^ k

def finiteRegularAbelianPGroup {Ω : Type*} [Fintype Ω]
    (p : ℕ) (R : Subgroup (Perm Ω)) : Prop :=
  displayedRegularCopy R ∧
    abelianPermutationCopy R ∧
      permutationPGroup p R

def generatedPair {Ω : Type*}
    (R T : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  Subgroup.closure ((R : Set (Perm Ω)) ∪ (T : Set (Perm Ω)))

def sylowPSubgroup {Ω : Type*}
    (p : ℕ) (X P : Subgroup (Perm Ω)) : Prop :=
  P ≤ X ∧
    permutationPGroup p P ∧
      ∀ Q : Subgroup (Perm Ω), Q ≤ X → permutationPGroup p Q →
        Nat.card Q ≤ Nat.card P

def conjugatedMembership {Ω : Type*}
    (x : Perm Ω) (T : Subgroup (Perm Ω)) (z : Perm Ω) : Prop :=
  ∃ t : T, z = x⁻¹ * (t : Perm Ω) * x

def commonSylowData {Ω : Type*}
    (p : ℕ) (R T X P : Subgroup (Perm Ω)) (x : Perm Ω) : Prop :=
  X = generatedPair R T ∧
    x ∈ X ∧
      sylowPSubgroup p X P ∧
        (R ≤ P) ∧
          (∀ t : T, x⁻¹ * (t : Perm Ω) * x ∈ P)

/-- The ambient image of the center of a permutation subgroup. -/
def ambientCenter {Ω : Type*}
    (P : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  (Subgroup.center P).map P.subtype

def centerContainedInRegularCopies {Ω : Type*}
    (R T : Subgroup (Perm Ω)) (P : Subgroup (Perm Ω)) (x : Perm Ω) : Prop :=
  ambientCenter P ≤ R ∧
    ∀ z : Perm Ω, z ∈ ambientCenter P → conjugatedMembership x T z

def orbitSet {Ω : Type*}
    (D : Subgroup (Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ d : D, d.1 x = y}

def orbitPartition {Ω : Type*}
    (D : Subgroup (Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, B = orbitSet D x}

def permutesPartition {Ω : Type*}
    (K : Set (Perm Ω)) (partition : Set (Set Ω)) : Prop :=
  ∀ g : Perm Ω, g ∈ K →
    ∀ B : Set Ω, B ∈ partition →
      ∃ B' : Set Ω, B' ∈ partition ∧ Set.image g B = B'

def commonSylowHypotheses {Ω : Type*} [Fintype Ω]
    (p : ℕ) (R T : Subgroup (Perm Ω)) : Prop :=
  Nat.Prime p ∧
    finiteRegularAbelianPGroup p R ∧
      finiteRegularAbelianPGroup p T

/-- Claim 41583: both displayed regular copies enter one Sylow p-subgroup,
with the required conjugating element retained. -/
def claim41583_sylowReduction : Prop :=
  ∀ (p : ℕ) (Ω : Type*) [Fintype Ω]
    (R T : Subgroup (Perm Ω)),
    commonSylowHypotheses p R T →
      let X := generatedPair R T
      ∃ (P : Subgroup (Perm Ω)) (x : Perm Ω),
        x ∈ X ∧
          sylowPSubgroup p X P ∧
            R ≤ P ∧
              (∀ t : T, x⁻¹ * (t : Perm Ω) * x ∈ P)

/-- Claim 41585: the center supplied by the common Sylow reduction is a
nontrivial subgroup contained in both regular copies. -/
def claim41585_nontrivialCommonCenter : Prop :=
  ∀ (p : ℕ) (Ω : Type*) [Fintype Ω]
    (R T : Subgroup (Perm Ω))
    (X P : Subgroup (Perm Ω)) (x : Perm Ω),
    commonSylowHypotheses p R T →
      commonSylowData p R T X P x →
        ambientCenter P ≠ ⊥ ∧
          centerContainedInRegularCopies R T P x

/-- Claim 41586: a central subgroup of order p is contained in the regular
copy and every one of its orbits has cardinality p. -/
def claim41586_centralOrderPSemiregular : Prop :=
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

/-- Claim 41587: the D-orbit partition is genuinely permuted by P, R, and
T^x, and every block has size p. -/
def claim41587_centralPrimeInvariantBlocks : Prop :=
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
end MathlibPlus.Open.ResearchFormalization.R1171
