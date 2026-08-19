import Mathlib

namespace MathlibPlus.Open.GroupTheory.PolycirculantX2Claim61293

noncomputable section

abbrev Perm (Ω : Type*) := Equiv.Perm Ω
abbrev F4 := GaloisField 2 2
abbrev F4VectorSpace := Fin 3 → F4

def transitivePermutationSubgroup {Ω : Type*}
    (G : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃ g : G, (g : Perm Ω) x = y

def fixedPointFree {Ω : Type*} (g : Perm Ω) : Prop :=
  ∀ x : Ω, g x ≠ x

def hasFixedPointFreePrimeOrderElement {Ω : Type*}
    (G : Subgroup (Perm Ω)) : Prop :=
  ∃ g : G,
    Nat.Prime (orderOf (g : Perm Ω)) ∧
      fixedPointFree (g : Perm Ω)

def elusivePermutationSubgroup {Ω : Type*}
    (G : Subgroup (Perm Ω)) : Prop :=
  ¬ hasFixedPointFreePrimeOrderElement G

def twoClosure {Ω : Type*}
    (G : Subgroup (Perm Ω)) : Set (Perm Ω) :=
  {q | ∀ x y : Ω, ∃ g : G,
    (g : Perm Ω) x = q x ∧ (g : Perm Ω) y = q y}

def twoClosedPermutationSubgroup {Ω : Type*}
    (G : Subgroup (Perm Ω)) : Prop :=
  ∀ q : Perm Ω, q ∈ twoClosure G → q ∈ G

def normalIn {Ω : Type*}
    (N G : Subgroup (Perm Ω)) : Prop :=
  N ≤ G ∧
    ∀ g : G, ∀ n : N,
      (g : Perm Ω) * (n : Perm Ω) * (g : Perm Ω)⁻¹ ∈ N

def minimalNormalIn {Ω : Type*}
    (N G : Subgroup (Perm Ω)) : Prop :=
  normalIn N G ∧
    ∀ M : Subgroup (Perm Ω),
      normalIn M G → M ≤ N → M = ⊥ ∨ M = N

def elementaryAbelianTwo {Ω : Type*}
    (E : Subgroup (Perm Ω)) : Prop :=
  (∀ a b : E, a * b = b * a) ∧
    (∀ a : E, a * a = 1)

def eOrbit {Ω : Type*}
    (E : Subgroup (Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ e : E, (e : Perm Ω) x = y}

def pointwiseStabilizerInEOrbit {Ω : Type*}
    (E : Subgroup (Perm Ω)) (x : Ω) : Set (Perm Ω) :=
  {e | e ∈ E ∧ ∀ y : Ω, y ∈ eOrbit E x → e y = y}

def multiplicityFreeEOrbitKernels {Ω : Type*}
    (E : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω,
    eOrbit E x ≠ eOrbit E y →
      pointwiseStabilizerInEOrbit E x ≠
        pointwiseStabilizerInEOrbit E y

def normalElementaryAbelianSix {Ω : Type*} [Fintype Ω]
    (G E : Subgroup (Perm Ω)) : Prop :=
  minimalNormalIn E G ∧
    elementaryAbelianTwo E ∧
    Nat.card E = 2 ^ 6

def x2BaseConfiguration {Ω : Type*} [Fintype Ω]
    (G E : Subgroup (Perm Ω)) : Prop :=
  transitivePermutationSubgroup G ∧
    elusivePermutationSubgroup G ∧
      normalElementaryAbelianSix G E ∧
        multiplicityFreeEOrbitKernels E

def kernelCoversE {Ω : Type*}
    (E : Subgroup (Perm Ω)) : Prop :=
  ∀ e : Perm Ω, e ∈ E →
    ∃ x : Ω, e ∈ pointwiseStabilizerInEOrbit E x

def conjugatePermutationSet {Ω : Type*}
    (g : Perm Ω) (S : Set (Perm Ω)) : Set (Perm Ω) :=
  {h | ∃ s, s ∈ S ∧ h = g * s * g⁻¹}

def kernelOrbitStructure {Ω : Type*}
    (G E : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃ g : G,
    conjugatePermutationSet (g : Perm Ω)
      (pointwiseStabilizerInEOrbit E x) =
      pointwiseStabilizerInEOrbit E y

def commonKernelDimension {Ω : Type*}
    (E : Subgroup (Perm Ω)) (k : ℕ) : Prop :=
  ∀ x : Ω,
    Set.ncard (pointwiseStabilizerInEOrbit E x) = 2 ^ k

def x2DimensionRange {Ω : Type*} [Fintype Ω]
    (E : Subgroup (Perm Ω)) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧ commonKernelDimension E k

def x2StructuralConsequences {Ω : Type*} [Fintype Ω]
    (G E : Subgroup (Perm Ω)) : Prop :=
  kernelCoversE E ∧
    kernelOrbitStructure G E ∧
      x2DimensionRange E

def f4PlaneKernel {Ω : Type*}
    (E : Subgroup (Perm Ω))
    (ψ : E ≃* Multiplicative F4VectorSpace)
    (W : Submodule F4 F4VectorSpace) : Set (Perm Ω) :=
  {q | ∃ e : E, q = (e : Perm Ω) ∧
    Multiplicative.toAdd (ψ e) ∈ W}

def invariantF4Structure {Ω : Type*}
    (G E : Subgroup (Perm Ω))
    (ψ : E ≃* Multiplicative F4VectorSpace) : Prop :=
  ∀ g : G, ∃ c : E ≃* E, ∃ L : F4VectorSpace ≃ₗ[F4] F4VectorSpace,
    (∀ e : E,
      (c e : Perm Ω) =
        (g : Perm Ω) * (e : Perm Ω) * (g : Perm Ω)⁻¹) ∧
      (∀ e : E,
        ψ (c e) = L.toAddEquiv.toMultiplicative (ψ e))

def f4PlaneKernelArrangement {Ω : Type*} [Fintype Ω]
    (G E : Subgroup (Perm Ω)) : Prop :=
  ∃ ψ : E ≃* Multiplicative F4VectorSpace,
    invariantF4Structure G E ψ ∧
      ∀ x : Ω, ∃ W : Submodule F4 F4VectorSpace,
        Module.finrank F4 W = 2 ∧
          Set.ncard (pointwiseStabilizerInEOrbit E x) = 16 ∧
            pointwiseStabilizerInEOrbit E x = f4PlaneKernel E ψ W

def claim61293 : Prop :=
  (∀ (Ω : Type*) [Fintype Ω]
      (G E : Subgroup (Perm Ω)),
    x2BaseConfiguration G E →
      x2StructuralConsequences G E) ∧
  (∀ (Ω : Type*) [Fintype Ω]
      (G E : Subgroup (Perm Ω)),
    x2BaseConfiguration G E →
      twoClosedPermutationSubgroup G →
        False) ∧
  (∀ (Ω : Type*) [Fintype Ω]
      (G E : Subgroup (Perm Ω)),
    x2BaseConfiguration G E →
      ¬ f4PlaneKernelArrangement G E →
        False)

end

end MathlibPlus.Open.GroupTheory.PolycirculantX2Claim61293
