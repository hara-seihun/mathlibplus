import Mathlib

namespace MathlibPlus.Open.GraphTheory.AdmittedBatch54734

noncomputable section

private def derivativeSpan {A W : Type*} [AddCommGroup A] [AddCommGroup W]
    [Module (ZMod 3) W] (phi : A → W) (a : A) : Submodule (ZMod 3) W :=
  Submodule.span (ZMod 3)
    {w : W | ∃ x : A, w = phi (x + a) - phi x - phi a}

private def slice {A W : Type*} (S : Set (A × W)) (a : A) : Set W :=
  {w | (a, w) ∈ S}

private def setAdd {W : Type*} [AddCommGroup W] (X Y : Set W) : Set W :=
  {w | ∃ x ∈ X, ∃ y ∈ Y, x + y = w}

private def triangularSwitch {A W : Type*} [AddCommGroup A] [AddCommGroup W]
    (phi : A → W) : A × W → A × W :=
  fun p => (p.1, p.2 + phi p.1)

private def cayleyAdj {A W : Type*} [AddCommGroup A] [AddCommGroup W]
    (S : Set (A × W)) (x y : A × W) : Prop :=
  y - x ∈ S

/-- Claim 54734: invariance of every fibre by the corresponding derivative
span makes the triangular switch a Cayley-graph isomorphism. -/
def triangularSwitchCayleyIsomorphism_claim54734 : Prop :=
  ∀ (A W : Type*) [Fintype A] [Fintype W]
    [AddCommGroup A] [AddCommGroup W]
    [Module (ZMod 3) A] [Module (ZMod 3) W]
    (phi : A → W) (S : Set (A × W)),
    phi 0 = 0 →
    (∀ a : A, phi (-a) = -phi a) →
    (∀ a : A, setAdd (slice S a) (derivativeSpan phi a : Set W) = slice S a) →
    Function.Bijective (triangularSwitch phi) ∧
      (∀ x y : A × W,
        cayleyAdj S x y ↔
          cayleyAdj (triangularSwitch phi '' S)
            (triangularSwitch phi x) (triangularSwitch phi y))

/-- Claim 54737: under full nonzero derivative span, an invariant connection
set is fixed by the triangular switch. -/
def fullDerivativeSpanFixesConnectionSet_claim54737 : Prop :=
  ∀ (A W : Type*) [Fintype A] [Fintype W]
    [AddCommGroup A] [AddCommGroup W]
    [Module (ZMod 3) A] [Module (ZMod 3) W]
    (phi : A → W) (S : Set (A × W)),
    phi 0 = 0 →
    (∀ a : A, phi (-a) = -phi a) →
    (∀ a : A, a ≠ 0 → derivativeSpan phi a = ⊤) →
    (∀ a : A, setAdd (slice S a) (derivativeSpan phi a : Set W) = slice S a) →
    triangularSwitch phi '' S = S

end
end MathlibPlus.Open.GraphTheory.AdmittedBatch54734
