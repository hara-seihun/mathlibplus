import Mathlib

namespace MathlibPlus.Open.GraphTheory.FiniteCIBatch

/-- An inverse-closed connection set for an undirected Cayley graph. -/
def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ x, x ∈ S → x⁻¹ ∈ S

/-- Isomorphism of the two undirected Cayley relations, written on the group
carrier rather than through a graph implementation. -/
def undirectedCayleyIsomorphism {G : Type*} [Group G]
    (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y : G,
    (x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T)

/-- The undirected Cayley-isomorphism property for a finite group.  Connection
sets are inverse-closed and omit the identity, as for simple undirected Cayley
graphs. -/
def undirectedCIGroup (G : Type*) [Group G] [Fintype G] : Prop :=
  ∀ S T : Set G,
    inverseClosed S → inverseClosed T →
    (1 : G) ∉ S → (1 : G) ∉ T →
    undirectedCayleyIsomorphism S T →
      ∃ φ : G ≃* G, φ '' S = T

abbrev cyclicGroup (n : ℕ) := Multiplicative (ZMod n)

/-- Claim 16561: `Q₈ × C_p` is an undirected CI-group for every odd prime. -/
def claim16561 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), p % 2 = 1 →
    letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
    undirectedCIGroup (QuaternionGroup 2 × cyclicGroup p)

/-- Claim 16566: `C_p × S₃` is an undirected CI-group for primes at least seven. -/
def claim16566 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), 7 ≤ p →
    letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
    undirectedCIGroup (cyclicGroup p × Equiv.Perm (Fin 3))

/-- Claim 16568: the order-five cyclic factor times the order-twelve
quaternion/dicyclic factor is CI. -/
def claim16568 : Prop :=
  letI : NeZero 5 := ⟨by decide⟩
  undirectedCIGroup (cyclicGroup 5 × QuaternionGroup 3)

/-- Claim 16569: `C₃² × Q₈` is an undirected CI-group. -/
def claim16569 : Prop :=
  letI : NeZero 3 := ⟨by decide⟩
  undirectedCIGroup (cyclicGroup 3 × cyclicGroup 3 × QuaternionGroup 2)

/-- Claim 16570: `C₃³ × Q₈` is an undirected CI-group. -/
def claim16570 : Prop :=
  letI : NeZero 3 := ⟨by decide⟩
  undirectedCIGroup
    (cyclicGroup 3 × cyclicGroup 3 × cyclicGroup 3 × QuaternionGroup 2)

/-- Claim 16571: `C₅² × Q₈` is an undirected CI-group. -/
def claim16571 : Prop :=
  letI : NeZero 5 := ⟨by decide⟩
  undirectedCIGroup (cyclicGroup 5 × cyclicGroup 5 × QuaternionGroup 2)

/-- Claim 16574: a non-CI subgroup obstructs the CI property of a finite group. -/
def claim16574 : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G] (H : Subgroup G),
    letI : Fintype H := Fintype.ofFinite H
    ¬ undirectedCIGroup H → ¬ undirectedCIGroup G

end MathlibPlus.Open.GraphTheory.FiniteCIBatch
