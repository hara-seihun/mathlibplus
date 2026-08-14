import Mathlib

namespace MathlibPlus.Open.OrbitRowReduction

variable {R T Ω I : Type*} [Group R] [Group T]
  [MulAction R Ω] [MulAction T Ω]


def invariantUnder (P : I → Ω → Ω → Prop) (G : Type*) [Group G]
    [MulAction G Ω] : Prop :=
  ∀ (i : I) (g : G) (x y : Ω),
    P i (g • x) (g • y) ↔ P i x y

def claim59555
    (θ : R ≃* T) (U : Ω ≃ Ω) (P : I → Ω → Ω → Prop) : Prop :=
  ((∀ r : R, ∀ x : Ω, U (r • x) = θ r • U x) ∧
    invariantUnder P R ∧ invariantUnder P T) →
    ∀ b : Ω,
      (∀ (i : I) (r : R) (y : Ω),
        P i (U (r • b)) (U y) ↔ P i (r • b) y) ↔
      (∀ (i : I) (y : Ω),
        P i (U b) (U y) ↔ P i b y)

end MathlibPlus.Open.OrbitRowReduction
