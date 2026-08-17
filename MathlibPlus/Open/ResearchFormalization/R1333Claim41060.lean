import MathlibPlus.Open.ResearchFormalization.BatchGroupClaims
import MathlibPlus.Open.ResearchFormalization.MinimumBlockAction
import MathlibPlus.Open.BatchFormalization.GroupClaims

namespace MathlibPlus.Open.ResearchFormalization.R1333

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.BatchFormalization

/-- A `G`-invariant partition of the finite permutation set, with the
partition data written explicitly. -/
def isGBlockSystem {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (blocks : Set (Set Ω)) : Prop :=
  (∀ B : Set Ω, B ∈ blocks → B.Nonempty) ∧
    (∀ B₁ : Set Ω, B₁ ∈ blocks →
      ∀ B₂ : Set Ω, B₂ ∈ blocks → B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
    ⋃₀ blocks = Set.univ ∧
    PreservesBlockSystem G blocks

/-- Nontriviality of a block system on a finite point set. -/
def isNontrivialGBlockSystem {Ω : Type*} [Fintype Ω]
    (blocks : Set (Set Ω)) : Prop :=
  ∃ B : Set Ω, B ∈ blocks ∧
    1 < Nat.card B ∧ Nat.card B < Nat.card Ω

/-- Imprimitivity, with no chosen block system hidden in the definition. -/
def isImprimitive {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ blocks : Set (Set Ω),
    isGBlockSystem G blocks ∧ isNontrivialGBlockSystem blocks

/-- The exact block-action kernel, not an arbitrary subgroup fixing blocks. -/
def isBlockActionKernel {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (blocks : Set (Set Ω))
    (K : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ g : Equiv.Perm Ω,
    g ∈ K ↔ g ∈ G ∧
      ∀ B : Set Ω, B ∈ blocks → g '' B = B

/-- Characteristicity of an ambient subgroup inside a permutation subgroup. -/
def isCharacteristicIn {α : Type*} [Group α]
    (P C : Subgroup α) : Prop :=
  P ≤ C ∧
    ∀ e : C ≃* C,
      Subgroup.map e.toMonoidHom (P.comap C.subtype) =
        P.comap C.subtype

/-- Cyclicity, exact order, and regularity of the quotient action on the
literal block set.  The action is recorded by its representative-independent
cosets: every ordered pair of blocks has exactly one quotient element that
carries the first block to the second. -/
def quotientRegularBlockAction {Ω : Type*}
    (C : Subgroup (Equiv.Perm Ω)) (Q : Subgroup C)
    (s : ℕ) (blocks : Set (Set Ω)) (hQ : Q.Normal) : Prop :=
  letI : Q.Normal := hQ
  IsCyclic (C ⧸ Q) ∧
    Nat.card (C ⧸ Q) = s ∧
      ∀ B B' : blocks,
        ∃! q : C ⧸ Q,
          ∃ c : C,
            QuotientGroup.mk c = q ∧
              (c : Equiv.Perm Ω) '' (B : Set Ω) = (B' : Set Ω)

/-- The prime-kernel branch with a characteristic order-`r` subgroup in the
block kernel and a cyclic order-`s` quotient acting regularly on blocks. -/
def primeKernelBranch {Ω : Type*} [Fintype Ω]
    (r s : ℕ) (C D : Subgroup (Equiv.Perm Ω))
    (blocks : Set (Set Ω)) (K : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ Cr Dr : Subgroup (Equiv.Perm Ω),
    C ⊓ K = Cr ∧ D ⊓ K = Dr ∧
      Nat.card Cr = r ∧ Nat.card Dr = r ∧
      isCharacteristicIn Cr C ∧ isCharacteristicIn Dr D ∧
      HasBlockOrbits Cr blocks ∧ HasBlockOrbits Dr blocks ∧
      (∀ B : Set Ω, B ∈ blocks →
        IsRegularOn (RestrictionSubgroup Cr B)) ∧
      (∀ B : Set Ω, B ∈ blocks →
        IsRegularOn (RestrictionSubgroup Dr B)) ∧
      ∃ hC : (Cr.comap C.subtype).Normal,
        ∃ hD : (Dr.comap D.subtype).Normal,
          quotientRegularBlockAction C (Cr.comap C.subtype)
            s blocks hC ∧
          quotientRegularBlockAction D (Dr.comap D.subtype)
            s blocks hD

/-- Claim 41060: every nontrivial block system has prime block size, and the
exact block-action kernel carries the characteristic local prime subgroups,
their literal common orbit partition, and the regular cyclic quotient action.
The two prime-size branches are stated symmetrically. -/
def claim41060 : Prop :=
  ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q →
    ∀ (Ω : Type*) [Fintype Ω], Fintype.card Ω = p * q →
      ∀ (G C D : Subgroup (Equiv.Perm Ω)),
        IsRegularCyclicAction (p * q) C →
        IsRegularCyclicAction (p * q) D →
        C ≤ G → D ≤ G → isImprimitive G →
        ∀ blocks : Set (Set Ω),
          isGBlockSystem G blocks →
          isNontrivialGBlockSystem blocks →
            (∀ B : Set Ω, B ∈ blocks →
              Nat.card B = p ∨ Nat.card B = q) ∧
            ((∀ B : Set Ω, B ∈ blocks → Nat.card B = q) →
              ∃ K : Subgroup (Equiv.Perm Ω),
                isBlockActionKernel G blocks K ∧
                  primeKernelBranch q p C D blocks K) ∧
            ((∀ B : Set Ω, B ∈ blocks → Nat.card B = p) →
              ∃ K : Subgroup (Equiv.Perm Ω),
                isBlockActionKernel G blocks K ∧
                  primeKernelBranch p q C D blocks K)

end MathlibPlus.Open.ResearchFormalization.R1333
