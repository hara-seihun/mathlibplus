import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim6367

/-- The rank-one equation with its displayed `x₂` coordinate. -/
def rankOneEquation {D : Type*} [Mul D]
    (x₂ A R : D) : Prop :=
  x₂ = A * R

/-- The zero-`x₂` rank-one face. -/
def zeroX₂Face {D : Type*} [Mul D] [Zero D]
    (A R : D) : Prop :=
  rankOneEquation (0 : D) A R

/-- The component obtained by setting the rooted factor `R` to zero. -/
def rZeroComponent {D : Type*} [Zero D] (A R : D) : Prop :=
  R = 0

/-- The component obtained by setting the rooted factor `A` to zero. -/
def aZeroComponent {D : Type*} [Zero D] (A R : D) : Prop :=
  A = 0

/-- The component selected by the packet on the degenerate face. -/
def informativeRankOneComponent {D : Type*} [Zero D] (A R : D) : Prop :=
  rZeroComponent A R

/-- Claim 6367: in an integral domain the zero-`x₂` rank-one face is the
union of the two factor-zero components, with `R = 0` as the informative
component. -/
def rankOneFaceDecomposition_claim6367 {D : Type*} [CommRing D]
    [IsDomain D] : Prop :=
  (∀ A R : D,
      zeroX₂Face A R ↔
        rZeroComponent A R ∨ aZeroComponent A R) ∧
    (∀ A R : D,
      informativeRankOneComponent A R ↔ rZeroComponent A R)

end MathlibPlus.Open.ResearchFormalization.Claim6367
