import Mathlib
import MathlibPlus.GraphTheory.CayleyCIHierarchy

namespace MathlibPlus.Open.ResearchFormalization.R4255Claim51201

noncomputable section

open scoped BigOperators

abbrev PrimeKernel (p r : ℕ) := Fin r → ZMod p
abbrev CyclicFourGroup (p r : ℕ) :=
  Multiplicative (ZMod 4 × PrimeKernel p r)
abbrev QuotientGroup (p r : ℕ) :=
  Multiplicative (ZMod 2 × PrimeKernel p r)

/-- The graph-automorphism predicate for a graph on the group carrier. -/
def graphAutomorphism {G : Type*} (Γ : SimpleGraph G)
    (f : Equiv.Perm G) : Prop :=
  ∀ x y : G, Γ.Adj x y ↔ Γ.Adj (f x) (f y)

/-- A permutation subgroup is a regular copy of the displayed group. -/
def regularCopy {G : Type*} [Group G]
    (L : Subgroup (Equiv.Perm G)) : Prop :=
  (∀ x y : G, ∃! l : L, (l : Equiv.Perm G) x = y) ∧
    ∃ e : G ≃* L, ∀ x y : G, e (x * y) = e x * e y

/-- A regular copy contained in the automorphism group of the graph. -/
def graphRegularCopy {G : Type*} [Group G]
    (Γ : SimpleGraph G) (L : Subgroup (Equiv.Perm G)) : Prop :=
  (∀ l : L, graphAutomorphism Γ (l : Equiv.Perm G)) ∧
    regularCopy L

/-- The orbit of a point under a permutation subgroup. -/
def subgroupOrbit {G : Type*}
    (L : Subgroup (Equiv.Perm G)) (x : G) : Set G :=
  {y | ∃ l : L, (l : Equiv.Perm G) x = y}

/-- The set of all orbits, used as the block partition carrier. -/
def orbitPartition {G : Type*}
    (L : Subgroup (Equiv.Perm G)) : Set (Set G) :=
  {O | ∃ x : G, O = subgroupOrbit L x}

/-- A literal unique order-two permutation inside a regular copy. -/
def uniqueInvolution {G : Type*} [Group G]
    (L : Subgroup (Equiv.Perm G)) (delta : Equiv.Perm G) : Prop :=
  delta ∈ L ∧
    delta ≠ 1 ∧
      delta * delta = 1 ∧
        ∀ delta' : Equiv.Perm G,
          delta' ∈ L → delta' ≠ 1 → delta' * delta' = 1 → delta' = delta

/-- The common-involution branch, with the unique order-two subgroups and
common orbit partition stated on the actual permutation carrier. -/
def commonInvolutionBranch {G : Type*} [Group G]
    (Γ : SimpleGraph G)
    (R T : Subgroup (Equiv.Perm G)) : Prop :=
  graphRegularCopy Γ R ∧
    graphRegularCopy Γ T ∧
      ∃ deltaR deltaT : Equiv.Perm G,
        uniqueInvolution R deltaR ∧
          uniqueInvolution T deltaT ∧
            orbitPartition
                (Subgroup.closure ({deltaR} : Set (Equiv.Perm G))) =
              orbitPartition
                (Subgroup.closure ({deltaT} : Set (Equiv.Perm G)))

/-- Conjugation of a permutation subgroup by a graph automorphism. -/
def conjugatedSubgroup {G : Type*} [Group G]
    (g : Equiv.Perm G) (L : Subgroup (Equiv.Perm G)) :
    Subgroup (Equiv.Perm G) :=
  Subgroup.map ((MulAut.conj g).toMonoidHom) L

/-- The right-Cayley graph of a connection set. -/
def rightCayleyGraph {G : Type*} [Group G]
    (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => x⁻¹ * y ∈ S)

/-- The common-involution bridge at a fixed odd prime and rank. -/
def commonInvolutionClosure (p r : ℕ) : Prop :=
  let G := CyclicFourGroup p r
  ∀ (S : Set G),
    (1 : G) ∉ S →
      (∀ s ∈ S, s⁻¹ ∈ S) →
        ∀ (R T : Subgroup (Equiv.Perm G)),
          commonInvolutionBranch (rightCayleyGraph S) R T →
            ∃ g : Equiv.Perm G,
              graphAutomorphism (rightCayleyGraph S) g ∧
                conjugatedSubgroup g R = T

/-- The conditional quotient bridge has no rank bound. -/
def conditionalQuotientBridge (p r : ℕ) (hp : 0 < p) : Prop :=
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  MathlibPlus.GraphTheory.IsCayleyCI2 (QuotientGroup p r) →
    commonInvolutionClosure p r

def rankOneTwoOrThree (r : ℕ) : Prop :=
  r = 1 ∨ r = 2 ∨ r = 3

/-- Claim 51201: the rank-one/two/three conditional instances and the
unbounded-rank reduction to the exact `CI^(2)` quotient premise. -/
def immediateConditionalQuotientInstances_claim51201 : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    (∀ r : ℕ, 1 ≤ r → rankOneTwoOrThree r →
      MathlibPlus.GraphTheory.IsCayleyCI2 (QuotientGroup p r)) →
      (∀ r : ℕ, 1 ≤ r → rankOneTwoOrThree r →
        commonInvolutionClosure p r) ∧
      (∀ r : ℕ, 1 ≤ r → conditionalQuotientBridge p r hp.pos)

end

end MathlibPlus.Open.ResearchFormalization.R4255Claim51201
