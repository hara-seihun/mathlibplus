import Mathlib

namespace MathlibPlus.Open.GraphTheory.TernaryHomogeneousCubicShear61035

noncomputable section

open scoped BigOperators

abbrev F3 := ZMod 3
abbrev Base := Fin 3 → F3
abbrev Exponent := Fin 3 → ℕ

def cubicExponentSet : Finset Exponent :=
  {![2, 1, 0], ![2, 0, 1], ![1, 2, 0], ![1, 0, 2],
    ![0, 2, 1], ![0, 1, 2], ![1, 1, 1]}

abbrev CubicExponent := {e : Exponent // e ∈ cubicExponentSet}

def cubicMonomial (x : Base) (e : Exponent) : F3 :=
  x 0 ^ e 0 * x 1 ^ e 1 * x 2 ^ e 2

def cubicForm {Z : Type*} [AddCommGroup Z] [Module F3 Z]
    (L0 : Base →ₗ[F3] Z) (z : CubicExponent → Z) : Base → Z :=
  fun x => L0 x + ∑ e : CubicExponent, cubicMonomial x e.1 • z e

def coefficientSpan {Z : Type*} [AddCommGroup Z] [Module F3 Z]
    (z : CubicExponent → Z) : Submodule F3 Z :=
  Submodule.span F3 (Set.range z)

def cubicDisplacementSpan {Z : Type*} [AddCommGroup Z] [Module F3 Z]
    (F : Base → Z) (b : Base) : Submodule F3 Z :=
  Submodule.span F3
    (Set.range (fun a : Base => F b + F a - F (a + b)))

def cubicRepairStatement {Z : Type*} [AddCommGroup Z] [Module F3 Z]
    (F : Base → Z) : Prop :=
  ∃ ell : Base →ₗ[F3] Z,
    ∀ b : Base, F b - ell b ∈ cubicDisplacementSpan F b

def cubicShear {Z : Type*} [AddCommGroup Z] [Module F3 Z]
    (F : Base → Z) : Base × Z → Base × Z :=
  fun x => (x.1, x.2 + F x.1)

def linearCubicShear {Z : Type*} [AddCommGroup Z] [Module F3 Z]
    (ell : Base →ₗ[F3] Z) : Base × Z → Base × Z :=
  fun x => (x.1, x.2 + ell x.1)

def pointedCayleyRelationIso {G : Type*} [AddGroup G]
    (q : G → G) (S T : Set G) : Prop :=
  q 0 = 0 ∧ Function.Bijective q ∧
    ∀ x y : G, y - x ∈ S ↔ q y - q x ∈ T

def identityFree {G : Type*} [AddZeroClass G] (S : Set G) : Prop :=
  0 ∉ S

def inverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

abbrev rankFibre (r : ℕ) := Fin (r - 3) → F3
abbrev rankCarrier (r : ℕ) := Base × rankFibre r

def homogeneousCubicShadowAtRank : Prop :=
  ∀ (r : ℕ), (r = 6 ∨ r = 7) →
    Module.finrank F3 (rankFibre r) ≤ 4 ∧
    ∀ (F : Base → rankFibre r)
      (L0 : Base →ₗ[F3] rankFibre r)
      (z : CubicExponent → rankFibre r),
      cubicForm L0 z = F →
      ∀ (S T : Set (rankCarrier r)),
        identityFree S → identityFree T →
        inverseClosed S → inverseClosed T →
        pointedCayleyRelationIso (cubicShear F) S T →
        ∃ ell : Base →ₗ[F3] rankFibre r,
          (∀ b : Base, F b - ell b ∈ cubicDisplacementSpan F b) ∧
          Set.image (linearCubicShear ell) S = T

def homogeneousCubicSpace : Submodule F3 (Base → F3) :=
  Submodule.span F3
    (Set.range (fun e : CubicExponent => fun x : Base => cubicMonomial x e.1))

def cubicEvaluationScalar {C : Submodule F3 (Base → F3)}
    (x : Base) : C →ₗ[F3] F3 :=
  (LinearMap.proj x).comp C.subtype

def cubicEvaluationFunction (C : Submodule F3 (Base → F3)) :
    Base → (C →ₗ[F3] F3) :=
  fun x => cubicEvaluationScalar (C := C) x

abbrev RepairUnknown (C : Submodule F3 (Base → F3)) :=
  Base →ₗ[F3] (C →ₗ[F3] F3)

abbrev RepairTarget (C : Submodule F3 (Base → F3)) :=
  ∀ b : Base,
    (C →ₗ[F3] F3) ⧸ cubicDisplacementSpan (cubicEvaluationFunction C) b

def repairSystemConsistent (C : Submodule F3 (Base → F3)) : Prop :=
  cubicRepairStatement (cubicEvaluationFunction C)

def repairSystemInconsistent (C : Submodule F3 (Base → F3)) : Prop :=
  ¬ repairSystemConsistent C

def repairCoefficientMap (C : Submodule F3 (Base → F3)) :
    RepairUnknown C →ₗ[F3] RepairTarget C :=
  LinearMap.pi (fun b =>
    (Submodule.mkQ (cubicDisplacementSpan
      (cubicEvaluationFunction C) b)).comp (LinearMap.applyₗ b))

def repairRightHandMap (C : Submodule F3 (Base → F3)) (b : Base) :
    F3 →ₗ[F3]
      ((C →ₗ[F3] F3) ⧸ cubicDisplacementSpan (cubicEvaluationFunction C) b) :=
  (Submodule.mkQ (cubicDisplacementSpan
    (cubicEvaluationFunction C) b)).comp
    (LinearMap.smulRight (LinearMap.id) (cubicEvaluationFunction C b))

def repairAugmentedMap (C : Submodule F3 (Base → F3)) :
    (RepairUnknown C × F3) →ₗ[F3] RepairTarget C :=
  LinearMap.pi (fun b =>
    ((Submodule.mkQ (cubicDisplacementSpan
        (cubicEvaluationFunction C) b)).comp (LinearMap.applyₗ b)).comp
      (LinearMap.fst F3 (RepairUnknown C) F3) +
    (repairRightHandMap C b).comp
      (LinearMap.snd F3 (RepairUnknown C) F3))

def repairCoefficientRank (C : Submodule F3 (Base → F3)) : ℕ :=
  Module.finrank F3 (LinearMap.range (repairCoefficientMap C))

def repairAugmentedRank (C : Submodule F3 (Base → F3)) : ℕ :=
  Module.finrank F3 (LinearMap.range (repairAugmentedMap C))

def coordinateFiveSpaces : Set (Submodule F3 (Base → F3)) :=
  {C | C ≤ homogeneousCubicSpace ∧ Module.finrank F3 C = 5}

def morrisScalarSpace : Submodule F3 (Base → F3) :=
  Submodule.span F3
    ({(fun x : Base => x 0 * (x 1) ^ 2),
      (fun x : Base => x 0 * (x 2) ^ 2),
      (fun x : Base => (x 1) ^ 2 * x 2),
      (fun x : Base => x 1 * (x 2) ^ 2),
      (fun x : Base => x 0 * x 1 * x 2)} : Set (Base → F3))

def claim_61035 : Prop :=
  (∀ (Z : Type*) [AddCommGroup Z] [Module F3 Z]
      [FiniteDimensional F3 Z]
      (F : Base → Z) (L0 : Base →ₗ[F3] Z)
      (z : CubicExponent → Z),
      cubicForm L0 z = F →
      Module.finrank F3 (coefficientSpan z) ≤ 4 →
      ∃ ell : Base →ₗ[F3] Z,
        (∀ b : Base, F b - ell b ∈ cubicDisplacementSpan F b) ∧
        ∀ (S T : Set (Base × Z)),
          pointedCayleyRelationIso (cubicShear F) S T →
          Set.image (linearCubicShear ell) S = T) ∧
  homogeneousCubicShadowAtRank ∧
  morrisScalarSpace ∈ coordinateFiveSpaces ∧
  Module.finrank F3 (morrisScalarSpace) = 5 ∧
  Set.ncard coordinateFiveSpaces = 99463 ∧
  Set.ncard {C : Submodule F3 (Base → F3) |
    C ∈ coordinateFiveSpaces ∧ repairSystemInconsistent C} = 13 ∧
  repairSystemInconsistent morrisScalarSpace ∧
  repairCoefficientRank morrisScalarSpace = 9 ∧
  repairAugmentedRank morrisScalarSpace = 10

end

end MathlibPlus.Open.GraphTheory.TernaryHomogeneousCubicShear61035
