import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.FrontierClaim61284

noncomputable section

/-- An orbit of a subgroup of a finite permutation group, written on the
literal permutation carrier. -/
def subgroupOrbit {Ω : Type*}
    (N : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ n : N, n.1 x = y}

/-- The exact binary 2-closure membership predicate. -/
def binaryTwoClosureMember {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) : Prop :=
  ∀ x y : Ω, ∃ g : G,
    σ x = g.1 x ∧ σ y = g.1 y

/-- Pairwise realizability transfer into the binary 2-closure, with ordered
orbit pairs and diagonal orbit pairs retained. -/
def claim61284 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω]
    (G N : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω),
    N ≤ G →
      (∀ x : Ω,
        Set.image σ (subgroupOrbit N x) = subgroupOrbit N x) →
      (∀ x y : Ω,
        ∃ e : N,
          (∀ u : subgroupOrbit N x, σ u = e.1 u) ∧
          (∀ v : subgroupOrbit N y, σ v = e.1 v)) →
      binaryTwoClosureMember G σ

end

end MathlibPlus.Open.ResearchFormalization.FrontierClaim61284
