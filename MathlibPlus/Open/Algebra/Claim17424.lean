import Mathlib

namespace MathlibPlus.Open.Algebra.Claim17424

open scoped BigOperators

noncomputable section

/-- The boundary of an edge chain on the finite path with vertices
`0,...,N` and edges `j : v_j - v_(j-1)`. -/
def pathBoundary {G : Type*} [AddCommGroup G]
    {N : ℕ} (H : Fin N → G) : Fin (N + 1) → G :=
  fun i =>
    ∑ j : Fin N,
      if i.1 = j.1 + 1 then H j
      else if i.1 = j.1 then -H j
      else 0

/-- The total mass of a finite event chain. -/
def totalMass {G : Type*} [AddCommGroup G]
    {N : ℕ} (E : Fin (N + 1) → G) : G :=
  ∑ i : Fin (N + 1), E i

/-- Membership in the image of the path boundary map. -/
def inPathBoundaryImage {G : Type*} [AddCommGroup G]
    {N : ℕ} (E : Fin (N + 1) → G) : Prop :=
  ∃ H : Fin N → G, pathBoundary H = E

/-- Claim 17424: on a finite path, an event chain is a boundary exactly when
its total mass is zero. -/
def claim17424 : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (N : ℕ)
    (E : Fin (N + 1) → G),
    inPathBoundaryImage E ↔ totalMass E = 0

end
end MathlibPlus.Open.Algebra.Claim17424
