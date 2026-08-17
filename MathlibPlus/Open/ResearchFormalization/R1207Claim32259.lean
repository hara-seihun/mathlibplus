import MathlibPlus.Open.Research.SylowPropagationPrimeLine

namespace MathlibPlus.Open.ResearchFormalization.R1207Claim32259

open MathlibPlus.Open.Research.SylowPropagationPrimeLine

/-- The orbit of a point under a subgroup of the ambient permutation group. -/
def orbitSet {Ω : Type*} {A : Subgroup (Equiv.Perm Ω)}
    (P : Subgroup A) (x : Ω) : Set Ω :=
  {y | ∃ p : P, ((p : A) : Equiv.Perm Ω) x = y}

/-- The literal family of all point-orbits of a subgroup. -/
def orbitPartition {Ω : Type*} {A : Subgroup (Equiv.Perm Ω)}
    (P : Subgroup A) : Set (Set Ω) :=
  Set.range (fun x : Ω => orbitSet P x)

/-- The subgroup has exactly the displayed block partition as its orbit
partition, without adding regularity on any block. -/
def hasOrbitPartition {Ω : Type*} {A : Subgroup (Equiv.Perm Ω)}
    (P : Subgroup A) (B : Finset (Set Ω)) : Prop :=
  orbitPartition P = (B : Set (Set Ω))

/-- Claim 32259: a common literal complement synchronizes a global prime
line. -/
def claim32259 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (A : Subgroup (Equiv.Perm Ω))
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (p : ℕ) (P Q L : Subgroup A),
    validBlockAction B A π →
    Nat.Prime p →
    P ≤ π.ker →
    Q ≤ π.ker →
    permutationPGroup p P →
    permutationPGroup p Q →
    abelianCopy P →
    abelianCopy Q →
    hasOrbitPartition P B →
    hasOrbitPartition Q B →
    transitiveLiteralComplement π L →
    (∀ q : Q, centralizesLiteral (q : A) L) →
    (∀ q : P, centralizesLiteral (q : A) L) →
    ∃ k : A,
      k ∈ π.ker ∧
        centralizesLiteral k L ∧
          ∃ D : Subgroup A,
            D ≤ P ∧
              Nat.card D = p ∧
                (∀ d : D,
                  ∃ q : Q,
                    (d : A) = conjugateBy k (q : A))

end MathlibPlus.Open.ResearchFormalization.R1207Claim32259
