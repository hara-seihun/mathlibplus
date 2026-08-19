import Mathlib

namespace MathlibPlus.Open.GraphTheory

noncomputable section

/-- The source connection slice at a base difference. -/
def triangularSourceSlice52683
    {A B W : Type*} (S : (A × B) → Set W)
    (u : A × B) : Set ((A × B) × W) :=
  {p | p.1 = u ∧ p.2 ∈ S u}

/-- The target fibre slice obtained by the triangular shear, including the
subgroup-valued error direction `H_u`. -/
def triangularTargetSlice52683
    {A B W : Type*} [AddCommGroup W]
    (S : (A × B) → Set W) (H : (A × B) → AddSubgroup W)
    (φ : (A × B) → W) (u : A × B) : Set W :=
  {w | ∃ v, v ∈ S u ∧ ∃ h, h ∈ H u ∧ w = v + φ u + h}

/-- Claim 52683: the explicit triangular fibre shear is a graph isomorphism
from the source Cayley connection slices to the target slices. -/
def triangularCayleyGraphIsomorphism : Prop :=
  ∀ {A B W : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup W]
    (S : (A × B) → Set W) (H : (A × B) → AddSubgroup W)
    (φ : (A × B) → W),
    (∀ u v h, v ∈ S u → h ∈ H u → v + h ∈ S u) →
    (∀ c u, φ (c + u) - φ c - φ u ∈ H u) →
    φ 0 = 0 →
    (∀ u, φ (-u) = -φ u) →
    (∀ u v, v ∈ S u ↔ -v ∈ S (-u)) →
    let source : Set ((A × B) × W) :=
      {p | p.2 ∈ S p.1}
    let target : Set ((A × B) × W) :=
      {p | p.2 ∈ triangularTargetSlice52683 S H φ p.1}
    ∃ e : (SimpleGraph.addCayley source ≃g
      SimpleGraph.addCayley target),
      ∀ p, e p = (p.1, p.2 + φ p.1)

end

end MathlibPlus.Open.GraphTheory
