import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.FiberProfiles

abbrev Base2 := Fin 3 → ZMod 2
abbrev Fiber3 := Fin 2 → ZMod 3
abbrev FiberProduct := Base2 × Fiber3

abbrev GL3_2 := Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)
abbrev GL2_3 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

def fiberPresentation (f : Equiv.Perm FiberProduct)
    (σ : Equiv.Perm Base2) (q : Base2 → Equiv.Perm Fiber3) : Prop :=
  σ 0 = 0 ∧ q 0 = 1 ∧
    ∀ v : Base2, ∀ b : Fiber3,
      f (v, b) = (σ v, q v b)

def normalizedFiberPreserving (f : Equiv.Perm FiberProduct) : Prop :=
  ∃ σ : Equiv.Perm Base2, ∃ q : Base2 → Equiv.Perm Fiber3,
    fiberPresentation f σ q

def activeFibers (q : Base2 → Equiv.Perm Fiber3) : Finset Base2 := by
  classical
  exact Finset.univ.filter (fun c => c ≠ 0 ∧ q c ≠ 1)

def normalized_one_active_profile (f : Equiv.Perm FiberProduct) : Prop :=
  ∃ σ : Equiv.Perm Base2, ∃ q : Base2 → Equiv.Perm Fiber3,
    fiberPresentation f σ q ∧ (activeFibers q).card ≤ 1

def displacementSpan (p : Equiv.Perm Fiber3) : Submodule (ZMod 3) Fiber3 :=
  Submodule.span (ZMod 3)
    {w : Fiber3 | ∃ t : Fiber3, w = t - p t + p 0}

def inverseClosedAdd (S : Finset FiberProduct) : Prop :=
  ∀ x : FiberProduct, x ∈ S ↔ -x ∈ S

def addConnection (S : Finset FiberProduct) : Prop :=
  0 ∉ S ∧ inverseClosedAdd S

def additiveCayleyGraph (S : Finset FiberProduct) : SimpleGraph FiberProduct :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

def imageUnder (f : Equiv.Perm FiberProduct) (S : Finset FiberProduct) : Finset FiberProduct := by
  classical
  exact S.image f

def realizesCayleyIsomorphism (f : Equiv.Perm FiberProduct)
    (S : Finset FiberProduct) : Prop :=
  ∃ h : additiveCayleyGraph S ≃g
      additiveCayleyGraph (imageUnder f S),
    h.toEquiv = f

def productLinearAction (M : GL3_2) (N : GL2_3)
    (x : FiberProduct) : FiberProduct :=
  ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x.1,
    (N : Matrix (Fin 2) (Fin 2) (ZMod 3)).mulVec x.2)

def productLinearImage (M : GL3_2) (N : GL2_3)
    (S : Finset FiberProduct) : Finset FiberProduct := by
  classical
  exact S.image (productLinearAction M N)

def every_normalized_one_active_profile_is_CI_harmless : Prop :=
  ∀ (f : Equiv.Perm FiberProduct) (S : Finset FiberProduct),
    normalized_one_active_profile f →
    addConnection S → addConnection (imageUnder f S) →
    realizesCayleyIsomorphism f S →
    ∃ M : GL3_2, ∃ N : GL2_3,
      productLinearImage M N S = imageUnder f S

def has_at_least_two_active_fibers (f : Equiv.Perm FiberProduct) : Prop :=
  ∀ σ : Equiv.Perm Base2, ∀ q : Base2 → Equiv.Perm Fiber3,
    fiberPresentation f σ q → (activeFibers q).card ≥ 2

def residual_fiber_preserving_failures_require_two_active_fibers : Prop :=
  ∀ (f : Equiv.Perm FiberProduct),
    normalizedFiberPreserving f →
    (∃ S : Finset FiberProduct,
      addConnection S ∧ addConnection (imageUnder f S) ∧
      realizesCayleyIsomorphism f S ∧
      ¬ ∃ M : GL3_2, ∃ N : GL2_3,
        productLinearImage M N S = imageUnder f S) →
    has_at_least_two_active_fibers f

end MathlibPlus.Open.ResearchFormalization.FiberProfiles
