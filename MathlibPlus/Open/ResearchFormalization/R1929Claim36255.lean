import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1929Claim36255

noncomputable section

abbrev LocalPermutation := Equiv.Perm (Fin 4)

/-- A permutation subgroup acts regularly on the four points. -/
def regularLocalAction (H : Subgroup LocalPermutation) : Prop :=
  ∀ x y : Fin 4, ∃! h : H, (h : LocalPermutation) x = y

/-- A cyclic regular subgroup of the local symmetric group. -/
def regularCyclicC4 (H : Subgroup LocalPermutation) : Prop :=
  Nat.card H = 4 ∧
    ∃ σ : LocalPermutation,
      σ ∈ H ∧ orderOf σ = 4 ∧
        H = Subgroup.closure ({σ} : Set LocalPermutation) ∧
          regularLocalAction H

/-- A generator of a specified local cyclic C4 subgroup. -/
def c4Generator (H : Subgroup LocalPermutation) (σ : LocalPermutation) : Prop :=
  σ ∈ H ∧ orderOf σ = 4 ∧
    H = Subgroup.closure ({σ} : Set LocalPermutation)

/-- The four-cycles in the natural action on `Fin 4`. -/
def fourCycle (σ : LocalPermutation) : Prop :=
  orderOf σ = 4

def sameC4GeneratorPair : Prop :=
  ∃ σ τ : LocalPermutation,
    fourCycle σ ∧ fourCycle τ ∧
      Subgroup.closure ({σ} : Set LocalPermutation) =
        Subgroup.closure ({τ} : Set LocalPermutation)

def distinctC4GeneratorPair : Prop :=
  ∃ σ τ : LocalPermutation,
    fourCycle σ ∧ fourCycle τ ∧
      Subgroup.closure ({σ} : Set LocalPermutation) ≠
        Subgroup.closure ({τ} : Set LocalPermutation)

/-- The centralizer of one permutation, written as a concrete finite carrier. -/
def centralizerOf (σ : LocalPermutation) : Set LocalPermutation :=
  {τ | τ * σ = σ * τ}

/-- The local enumeration and the generated-group alternatives. -/
def localC4Enumeration : Prop :=
  Nat.card {σ : LocalPermutation // fourCycle σ} = 6 ∧
    Nat.card {H : Subgroup LocalPermutation // regularCyclicC4 H} = 3 ∧
    Nat.card
        {p : LocalPermutation × LocalPermutation //
          fourCycle p.1 ∧ fourCycle p.2 ∧
            Subgroup.closure ({p.1} : Set LocalPermutation) =
              Subgroup.closure ({p.2} : Set LocalPermutation)} = 12 ∧
    Nat.card
        {p : LocalPermutation × LocalPermutation //
          fourCycle p.1 ∧ fourCycle p.2 ∧
            Subgroup.closure ({p.1} : Set LocalPermutation) ≠
              Subgroup.closure ({p.2} : Set LocalPermutation)} = 24 ∧
    (∀ σ τ : LocalPermutation,
      fourCycle σ → fourCycle τ →
        Subgroup.closure ({σ} : Set LocalPermutation) =
            Subgroup.closure ({τ} : Set LocalPermutation) →
          Nat.card (Subgroup.closure ({σ, τ} : Set LocalPermutation)) = 4) ∧
    (∀ σ τ : LocalPermutation,
      fourCycle σ → fourCycle τ →
        Subgroup.closure ({σ} : Set LocalPermutation) ≠
            Subgroup.closure ({τ} : Set LocalPermutation) →
          Subgroup.closure ({σ, τ} : Set LocalPermutation) = ⊤) ∧
    (∀ σ : LocalPermutation, fourCycle σ →
      Nat.card
          (Subgroup.normalizer
            (↑(Subgroup.closure ({σ} : Set LocalPermutation)) :
              Set LocalPermutation)) = 8) ∧
    (∀ σ : LocalPermutation, fourCycle σ →
      Nat.card {τ : LocalPermutation // τ ∈ centralizerOf (σ ^ 2)} = 8)

/-- The involution inside a local C4 kernel. -/
def localInvolution (H : Subgroup LocalPermutation) (ι : LocalPermutation) : Prop :=
  ι ∈ H ∧ orderOf ι = 2

/-- The orbit partition of a subgroup on the local four-point block. -/
def localOrbit (J : Subgroup LocalPermutation) (x : Fin 4) : Set (Fin 4) :=
  {y | ∃ j : J, (j : LocalPermutation) x = y}

def localCosetPartition (J : Subgroup LocalPermutation) : Set (Set (Fin 4)) :=
  {P | ∃ x : Fin 4, P = localOrbit J x}

/-- A common C2 coset partition is represented by the two unique local
involutions and their orbit partitions. -/
def commonC2CosetPartition
    (H K : Subgroup LocalPermutation) : Prop :=
  ∃ ιH ιK : LocalPermutation,
    localInvolution H ιH ∧ localInvolution K ιK ∧
      localCosetPartition (Subgroup.closure ({ιH} : Set LocalPermutation)) =
        localCosetPartition (Subgroup.closure ({ιK} : Set LocalPermutation))

/-- A common C2 refinement on every common block. -/
def commonC2Refinement {B : Type*}
    (R T : B → Subgroup LocalPermutation) : Prop :=
  ∃ J : B → Subgroup LocalPermutation,
    ∀ b : B, ∃ ι : LocalPermutation,
      localInvolution (R b) ι ∧
        J b = Subgroup.closure ({ι} : Set LocalPermutation) ∧
          J b ≤ R b ∧ J b ≤ T b

/-- Claim 36255: the exact S4 local census together with the common-involution
and square-mismatched permutation-fibre dichotomy.  The branch is stated on
permutation kernels; it does not assert a nonsplit extension of an abstract
product group. -/
def claim36255 : Prop :=
  localC4Enumeration ∧
    ∀ {B : Type*} [Fintype B]
      (R T : B → Subgroup LocalPermutation),
      (∀ b : B, regularCyclicC4 (R b) ∧ regularCyclicC4 (T b)) →
      ((∀ b : B, R b = T b) →
        commonC2Refinement R T ∧
          (∀ b : B, ∀ ιR ιT : LocalPermutation,
            c4Generator (R b) ιR → c4Generator (T b) ιT →
              ιR ^ 2 = ιT ^ 2)) ∧
      ((∃ b : B, R b ≠ T b) →
        ∃ b : B,
          R b ≠ T b ∧
            (∀ ιR ιT : LocalPermutation,
              c4Generator (R b) ιR → c4Generator (T b) ιT →
                ιR ^ 2 ≠ ιT ^ 2 ∧
                  ¬ commonC2CosetPartition (R b) (T b)))

end

end MathlibPlus.Open.ResearchFormalization.R1929Claim36255
