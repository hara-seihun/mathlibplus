import MathlibPlus.Open.LinearAlgebra.Claim4835

namespace MathlibPlus.Open.ResearchFormalization.ProfileLattice4833

open MathlibPlus.Open.LinearAlgebra.Claim4835

noncomputable section

/-- The quadratic anchor at coordinate `i`. -/
def quadraticAnchor (i : ℕ) : ℕ := 2 * i ^ 2

/-- The coordinatewise node attached to a finite multiplicity profile. -/
def profileNode (m : Profile) (i : ℕ) : ℕ :=
  quadraticAnchor i + m i

/-- The coordinatewise order on finitely supported multiplicity vectors. -/
def coordinatewiseLE (m n : Profile) : Prop :=
  ∀ i : ℕ, m i ≤ n i

/-- The single-coordinate edge in direction `i`. -/
def profileEdge (m : Profile) (i : ℕ) : Profile := edge i m

/-- Claim 4833: finite multiplicity profiles are the coordinatewise lattice
based at the quadratic anchors, and the displayed single-coordinate edges
increment exactly one coordinate. -/
def multiplicityProfileLattice_claim4833 : Prop :=
  (∀ m n : Profile, (m ≤ n ↔ coordinatewiseLE m n)) ∧
    (∀ m n : Profile,
      coordinatewiseLE m n ↔ ∃ d : Profile, n = m + d) ∧
    (∀ (m : Profile) (i : ℕ),
      profileNode (profileEdge m i) i = profileNode m i + 1 ∧
        ∀ j : ℕ, j ≠ i → profileNode (profileEdge m i) j = profileNode m j)

end

end MathlibPlus.Open.ResearchFormalization.ProfileLattice4833
