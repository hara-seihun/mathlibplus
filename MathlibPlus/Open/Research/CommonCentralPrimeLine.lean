import Mathlib
import MathlibPlus.Open.GroupTheory.RegularBlockSubgroups

namespace MathlibPlus.Open.Research.CommonCentralPrimeLine

abbrev Permutation (Ω : Type*) := Equiv.Perm Ω

/-- The same literal block-action carrier used for the common-complement
 argument. -/
def validBlockAction {Ω : Type*} [Fintype Ω]
    (B : Finset (Set Ω))
    (A : Subgroup (Permutation Ω))
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B)) : Prop :=
  MathlibPlus.Open.finiteBlockSystem B ∧
    (∀ a : A, ∀ U : MathlibPlus.Open.blockType B,
      ((π a) U).1 = (a : Permutation Ω) '' U.1)

def regularKernelCopy {Ω : Type*} [Fintype Ω]
    {B : Finset (Set Ω)}
    {A : Subgroup (Permutation Ω)}
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (P : Subgroup A) : Prop :=
  P ≤ π.ker ∧
    (∀ U : MathlibPlus.Open.blockType B,
      ∀ x y : Ω, x ∈ U.1 → y ∈ U.1 →
        ∃! p : P, ((p : A) : Permutation Ω) x = y)

def permutationPGroup {Ω : Type*} [Fintype Ω]
    {A : Subgroup (Permutation Ω)}
    (p : ℕ) (U : Subgroup A) : Prop :=
  ∀ u : U, ∃ n : ℕ,
    orderOf (((u : U) : A) : Permutation Ω) = p ^ n

def abelianCopy {Ω : Type*}
    {A : Subgroup (Permutation Ω)} (P : Subgroup A) : Prop :=
  ∀ p q : P, (p : A) * (q : A) = (q : A) * (p : A)

def centralizesLiteral {Ω : Type*}
    {A : Subgroup (Permutation Ω)}
    (g : A) (L : Subgroup A) : Prop :=
  ∀ l : L, g * (l : A) = (l : A) * g

def transitiveLiteralComplement {Ω : Type*} [Fintype Ω]
    {B : Finset (Set Ω)}
    {A : Subgroup (Permutation Ω)}
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (L : Subgroup A) : Prop :=
  ∀ U V : MathlibPlus.Open.blockType B,
    ∃ l : L, (π (l : A)) U = V

/-- An internal direct product copy: the two factors commute, intersect
 trivially, and act regularly through their join. -/
def regularDirectProduct {Ω : Type*} [Fintype Ω]
    {A : Subgroup (Permutation Ω)}
    (P L : Subgroup A) : Prop :=
  (∀ p : P, ∀ l : L,
    (p : A) * (l : A) = (l : A) * (p : A)) ∧
  P ⊓ L = ⊥ ∧
  (∀ x y : Ω, ∃! g : ↥(P ⊔ L),
    ((g : A) : Permutation Ω) x = y)

def conjugateBy {Ω : Type*}
    {A : Subgroup (Permutation Ω)} (k g : A) : A :=
  k⁻¹ * g * k

def conjugatedCopy {Ω : Type*}
    {A : Subgroup (Permutation Ω)}
    (Q L : Subgroup A) (k : A) : Subgroup A :=
  Subgroup.closure
    ({g : A | ∃ q : Q, g = conjugateBy k (q : A)} ∪
      (L : Set A))

/-- The orbit set of a point under a subgroup of the ambient permutation
 group. -/
def subgroupOrbit {Ω : Type*}
    {A : Subgroup (Permutation Ω)}
    (D : Subgroup A) (x : Ω) : Set Ω :=
  {y | ∃ d : D, (((d : D) : A) : Permutation Ω) x = y}

/-- A prime-line block system: the D-orbits partition Ω, have prime size,
 and are blocks for both displayed copies. -/
def commonPrimeLineOrbitSystem {Ω : Type*} [Fintype Ω]
    {A : Subgroup (Permutation Ω)}
    (D S T : Subgroup A) (p : ℕ) : Prop :=
  (∀ x : Ω, (subgroupOrbit D x).ncard = p) ∧
  (∀ x y : Ω,
    y ∈ subgroupOrbit D x ↔ subgroupOrbit D y = subgroupOrbit D x) ∧
  (∀ g : S, ∀ x : Ω,
    (((g : S) : A) : Permutation Ω) '' subgroupOrbit D x =
      subgroupOrbit D ((((g : S) : A) : Permutation Ω) x)) ∧
  (∀ g : T, ∀ x : Ω,
    (((g : T) : A) : Permutation Ω) '' subgroupOrbit D x =
      subgroupOrbit D ((((g : T) : A) : Permutation Ω) x))

def centralSubgroupIn {Ω : Type*}
    {A : Subgroup (Permutation Ω)}
    (D S : Subgroup A) : Prop :=
  D ≤ S ∧ ∀ d : D, ∀ s : S,
    (d : A) * (s : A) = (s : A) * (d : A)

/-- Claim 42032: a common literal complement produces, after a centralizing
 conjugation, one common central prime-line block system for the two regular
 direct products. -/
def claim_42032 : Prop :=
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
    regularDirectProduct P L →
    regularDirectProduct Q L →
    ∃ k : A, k ∈ π.ker ∧
      (∀ l : L, conjugateBy k (l : A) = (l : A)) ∧
      ∃ D : Subgroup A,
        D ≤ P ∧
        (∀ d : D, ∃ q : Q,
          (d : D) = conjugateBy k ((q : Q) : A)) ∧
        Nat.card D = p ∧
        centralSubgroupIn D (P ⊔ L) ∧
        centralSubgroupIn D (conjugatedCopy Q L k) ∧
        commonPrimeLineOrbitSystem D (P ⊔ L)
          (conjugatedCopy Q L k) p

end MathlibPlus.Open.Research.CommonCentralPrimeLine
