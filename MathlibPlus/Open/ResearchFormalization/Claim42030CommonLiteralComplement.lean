import Mathlib
import MathlibPlus.Open.GroupTheory.RegularBlockSubgroups

namespace MathlibPlus.Open.ResearchFormalization.Claim42030

noncomputable section

abbrev Permutation (Ω : Type*) := Equiv.Perm Ω

/-- A finite block system together with the literal action induced by the
ambient permutation group. -/
def validBlockAction {Ω : Type*} [Fintype Ω]
    (B : Finset (Set Ω))
    (X : Subgroup (Permutation Ω))
    (π : X →* Equiv.Perm (MathlibPlus.Open.blockType B)) : Prop :=
  MathlibPlus.Open.finiteBlockSystem B ∧
    (∀ x : X, ∀ U : MathlibPlus.Open.blockType B,
      ((π x) U).1 = (x : Permutation Ω) '' U.1)

def subgroupOrbit {Ω : Type*}
    (X : Subgroup (Permutation Ω))
    (P : Subgroup X) (x : Ω) : Set Ω :=
  {y | ∃ g : P, ((g : X) : Permutation Ω) x = y}

def hasOrbitPartition {Ω : Type*}
    (X : Subgroup (Permutation Ω))
    (P : Subgroup X) (B : Finset (Set Ω)) : Prop :=
  (∀ x : Ω, ∃ U : Set Ω, U ∈ B ∧ subgroupOrbit X P x = U) ∧
    (∀ U : Set Ω, U ∈ B → ∃ x : Ω, subgroupOrbit X P x = U)

def actsTransitivelyOnBlocks {Ω : Type*} [Fintype Ω]
    {B : Finset (Set Ω)}
    {X : Subgroup (Permutation Ω)}
    (π : X →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (L : Subgroup X) : Prop :=
  ∀ U V : MathlibPlus.Open.blockType B,
    ∃ l : L, (π (l : X)) U = V

def isAbelianSubgroup {Ω : Type*}
    {X : Subgroup (Permutation Ω)} (P : Subgroup X) : Prop :=
  ∀ p q : P, (p : X) * (q : X) = (q : X) * (p : X)

def isPGroup {Ω : Type*}
    {X : Subgroup (Permutation Ω)} (p : ℕ) (P : Subgroup X) : Prop :=
  Nat.Prime p ∧
    ∀ g : P, ∃ n : ℕ,
      orderOf (((g : P) : X) : Permutation Ω) = p ^ n

def centralizesLiteral {Ω : Type*}
    {X : Subgroup (Permutation Ω)}
    (g : X) (L : Subgroup X) : Prop :=
  ∀ l : L, g * (l : X) = (l : X) * g

def conjugateBy {Ω : Type*}
    {X : Subgroup (Permutation Ω)} (k g : X) : X :=
  k⁻¹ * g * k

/-- A common literal complement produces a centralizing conjugate whose
intersection with the first p-group contains a subgroup of order p. -/
def claim42030 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (X : Subgroup (Permutation Ω))
    (π : X →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (p : ℕ) (P Q L : Subgroup X),
    validBlockAction B X π →
    P ≤ π.ker →
    Q ≤ π.ker →
    hasOrbitPartition X P B →
    hasOrbitPartition X Q B →
    isPGroup p P →
    isPGroup p Q →
    isAbelianSubgroup P →
    isAbelianSubgroup Q →
    actsTransitivelyOnBlocks π L →
    (∀ q : Q, centralizesLiteral (q : X) L) →
    (∀ q : P, centralizesLiteral (q : X) L) →
      ∃ k : X,
        k ∈ π.ker ∧
          centralizesLiteral k L ∧
          ∃ D : Subgroup X,
            D ≤ P ∧
            (∀ d : D, ∃ q : Q,
              (d : X) = conjugateBy k (q : X)) ∧
            Nat.card D = p

end
end MathlibPlus.Open.ResearchFormalization.Claim42030
