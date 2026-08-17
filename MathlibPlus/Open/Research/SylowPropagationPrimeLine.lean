import Mathlib
import MathlibPlus.Open.GroupTheory.RegularBlockSubgroups

namespace MathlibPlus.Open.Research.SylowPropagationPrimeLine

abbrev Permutation (Ω : Type*) := Equiv.Perm Ω

/-- A homomorphism recording the action of an ambient permutation group on a
 finite block system. -/
def validBlockAction {Ω : Type*} [Fintype Ω]
    (B : Finset (Set Ω))
    (A : Subgroup (Permutation Ω))
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B)) : Prop :=
  MathlibPlus.Open.finiteBlockSystem B ∧
    (∀ a : A, ∀ U : MathlibPlus.Open.blockType B,
      ((π a) U).1 = (a : Permutation Ω) '' U.1)

/-- Regularity of a kernel copy on every member of the displayed block
 partition. -/
def regularKernelCopy {Ω : Type*} [Fintype Ω]
    {B : Finset (Set Ω)}
    {A : Subgroup (Permutation Ω)}
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (P : Subgroup A) : Prop :=
  P ≤ π.ker ∧
    (∀ U : MathlibPlus.Open.blockType B,
      ∀ x y : Ω, x ∈ U.1 → y ∈ U.1 →
        ∃! p : P, ((p : A) : Permutation Ω) x = y)

/-- The local p-group condition used in the Sylow argument. -/
def permutationPGroup {Ω : Type*} [Fintype Ω]
    {A : Subgroup (Permutation Ω)}
    (p : ℕ) (U : Subgroup A) : Prop :=
  ∀ u : U, ∃ n : ℕ,
    orderOf (((u : U) : A) : Permutation Ω) = p ^ n

/-- Literal commutation with the chosen complement. -/
def centralizesLiteral {Ω : Type*}
    {A : Subgroup (Permutation Ω)}
    (g : A) (L : Subgroup A) : Prop :=
  ∀ l : L, g * (l : A) = (l : A) * g

/-- Abelianity of a permutation subgroup written in its ambient group. -/
def abelianCopy {Ω : Type*}
    {A : Subgroup (Permutation Ω)} (P : Subgroup A) : Prop :=
  ∀ p q : P, (p : A) * (q : A) = (q : A) * (p : A)

/-- Transitivity of the literal complement on the displayed blocks. -/
def transitiveLiteralComplement {Ω : Type*} [Fintype Ω]
    {B : Finset (Set Ω)}
    {A : Subgroup (Permutation Ω)}
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (L : Subgroup A) : Prop :=
  ∀ U V : MathlibPlus.Open.blockType B,
    ∃ l : L, (π (l : A)) U = V

/-- Equality of two ambient permutations after restriction to one block. -/
def sameRestriction {Ω : Type*}
    {B : Finset (Set Ω)}
    {A : Subgroup (Permutation Ω)}
    (g h : A) (U : MathlibPlus.Open.blockType B) : Prop :=
  ∀ x : Ω, x ∈ U.1 →
    (g : Permutation Ω) x = (h : Permutation Ω) x

/-- The conjugate used for the notation `Q^k` in the admitted records. -/
def conjugateBy {Ω : Type*}
    {A : Subgroup (Permutation Ω)} (k g : A) : A :=
  k⁻¹ * g * k

/-- Faithfulness of restriction on one block, isolated as the local step of
 the propagation mechanism. -/
def faithfulRestriction {Ω : Type*} [Fintype Ω]
    {B : Finset (Set Ω)}
    {A : Subgroup (Permutation Ω)}
    (P : Subgroup A) (U : MathlibPlus.Open.blockType B) : Prop :=
  ∀ p : P,
    sameRestriction (p : A) (1 : A) U → (p : A) = 1

/-- The conclusion supplied by Sylow conjugacy, the local common centre, and
 propagation across the transitive complement. -/
def sylowPropagationConclusion {Ω : Type*} [Fintype Ω]
    {B : Finset (Set Ω)}
    {A : Subgroup (Permutation Ω)}
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (p : ℕ) (P Q L : Subgroup A) : Prop :=
  ∃ (U₀ : MathlibPlus.Open.blockType B) (k : A) (U : Subgroup A),
    k ∈ π.ker ∧
    centralizesLiteral k L ∧
    U ≤ π.ker ∧
    (∀ u : U, centralizesLiteral ((u : U) : A) L) ∧
    permutationPGroup p U ∧
    P ≤ U ∧
    (∀ q : Q, conjugateBy k (q : A) ∈ U) ∧
    (∃ dP : P, ∃ dQ : Q,
      ((dP : P) : A) ≠ 1 ∧
      ((dQ : Q) : A) ≠ 1 ∧
      sameRestriction ((dP : P) : A)
        (conjugateBy k ((dQ : Q) : A)) U₀ ∧
      (∀ V : MathlibPlus.Open.blockType B,
        sameRestriction ((dP : P) : A)
          (conjugateBy k ((dQ : Q) : A)) V) ∧
      ((dP : P) : A) = conjugateBy k ((dQ : Q) : A))

/-- Claim 42031: Sylow conjugacy in the centralizer of the literal
 complement, followed by faithful local restriction and transitive
 propagation, produces the global matching permutation. -/
def claim_42031 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (A : Subgroup (Permutation Ω))
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (p : ℕ) (P Q L : Subgroup A),
    validBlockAction B A π →
    Nat.Prime p →
    regularKernelCopy π P →
    regularKernelCopy π Q →
    abelianCopy P →
    abelianCopy Q →
    permutationPGroup p P →
    permutationPGroup p Q →
    transitiveLiteralComplement π L →
    (∀ q : Q, centralizesLiteral (q : A) L) →
    (∀ q : P, centralizesLiteral (q : A) L) →
    sylowPropagationConclusion π p P Q L

end MathlibPlus.Open.Research.SylowPropagationPrimeLine
