import Mathlib

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- Affine images of finite support layers in F₃². -/
abbrev V3 := Fin 2 → ZMod 3

def affineImage3 (A : V3 ≃ₗ[ZMod 3] V3) (b : V3)
    (s : Finset V3) : Finset V3 :=
  s.image (fun x => A x + b)

def affineLayerOrbitCount3 (k : ℕ) (N : ℕ) : Prop :=
  ∃ reps : Fin N → Finset V3,
    (∀ i, (reps i).card = k) ∧
      (∀ s : Finset V3, s.card = k →
        ∃! i : Fin N, ∃ A : V3 ≃ₗ[ZMod 3] V3, ∃ b : V3,
          s = affineImage3 A b (reps i))

def claim28768 : Prop :=
  affineLayerOrbitCount3 3 2 ∧ affineLayerOrbitCount3 4 2
end MathlibPlus.Open.ResearchFormalization.Batch
