import Mathlib

namespace MathlibPlus.Open.ResearchHolonomy

noncomputable section

/-- The joint map used by the scalar-response claims. -/
def jointMap {C W Z : Type*} [Semiring ℚ]
    [AddCommMonoid C] [AddCommMonoid W] [AddCommMonoid Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z) : C →ₗ[ℚ] W × Z :=
  LinearMap.prod L A

/-- The physical response holonomy `A (ker L)`. -/
def physicalHolonomy {C W Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z) : Submodule ℚ Z :=
  LinearMap.range (A.domRestrict (LinearMap.ker L))

/-- A linear cokernel, represented by the quotient by the range. -/
abbrev linearCoker {X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y] [Module ℚ X] [Module ℚ Y]
    (f : X →ₗ[ℚ] Y) : Type _ := Y ⧸ LinearMap.range f

/-- The zero-scalar target class `[(0,a)]` in the joint cokernel. -/
def zeroScalarTarget {C W Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z) (a : Z) :
    linearCoker (jointMap L A) :=
  (LinearMap.range (jointMap L A)).mkQ (0, a)

/-- The subspace of the joint cokernel represented by zero-scalar classes. -/
def zeroScalarClasses {C W Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z) :
    Submodule ℚ (linearCoker (jointMap L A)) :=
  LinearMap.range
    ((LinearMap.range (jointMap L A)).mkQ.comp (LinearMap.inr ℚ W Z))

/-- The exact-sequence assertion for the zero-scalar slice.  The displayed
maps are required to send `[z]` to `[(0,z)]` and `[(w,a)]` to `[w]`. -/
def zeroScalarShortExact {C W Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z) : Prop :=
  ∃ (ι : (Z ⧸ physicalHolonomy L A) →ₗ[ℚ]
        linearCoker (jointMap L A))
    (π : linearCoker (jointMap L A) →ₗ[ℚ]
        linearCoker L),
    Function.Injective ι ∧
    Function.Surjective π ∧
    π.comp ι = 0 ∧
    LinearMap.range ι = LinearMap.ker π ∧
    (∀ z : Z,
      ι ((physicalHolonomy L A).mkQ z) = zeroScalarTarget L A z) ∧
    (∀ w : W, ∀ a : Z,
      π ((LinearMap.range (jointMap L A)).mkQ (w, a)) =
        (LinearMap.range L).mkQ w)

/-- R-5089.1: the finite-dimensional rational scalar-response setup, including
`J=(L,A)`, its physical holonomy, and the zero-scalar target class. -/
def claim54996 : Prop :=
  ∀ (C W Z : Type*)
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    [FiniteDimensional ℚ C] [FiniteDimensional ℚ W] [FiniteDimensional ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z),
    jointMap L A = LinearMap.prod L A ∧
    physicalHolonomy L A =
      LinearMap.range (A.domRestrict (LinearMap.ker L)) ∧
    ∀ a : Z,
      zeroScalarTarget L A a =
        (LinearMap.range (jointMap L A)).mkQ (0, a)

/-- R-5089.2: the canonical short exact sequence for the zero-scalar slice. -/
def claim54997 : Prop :=
  ∀ (C W Z : Type*)
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    [FiniteDimensional ℚ C] [FiniteDimensional ℚ W] [FiniteDimensional ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z),
    zeroScalarShortExact L A

/-- R-5089.3: zero is holonomy membership, together with the rank formula and
its one-dimensional and arbitrary-response consequences. -/
def claim54998 : Prop :=
  ∀ (C W Z : Type*)
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    [FiniteDimensional ℚ C] [FiniteDimensional ℚ W] [FiniteDimensional ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z),
    (∀ a : Z,
      zeroScalarTarget L A a = 0 ↔ a ∈ physicalHolonomy L A) ∧
    Module.finrank ℚ (physicalHolonomy L A) =
      Module.finrank ℚ (LinearMap.range (jointMap L A)) -
        Module.finrank ℚ (LinearMap.range L) ∧
    (Module.finrank ℚ Z = 1 →
      ∀ a : Z, a ≠ 0 →
        (zeroScalarTarget L A a = 0 ↔
          Module.finrank ℚ (LinearMap.range (jointMap L A)) >
            Module.finrank ℚ (LinearMap.range L))) ∧
    (physicalHolonomy L A = ⊤ ↔
      Module.finrank ℚ (LinearMap.range (jointMap L A)) -
          Module.finrank ℚ (LinearMap.range L) = Module.finrank ℚ Z)

/-- The dual short exact sequence, with its scalar injection and response
projection written on representatives. -/
def dualZeroScalarShortExact {C W Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z) : Prop :=
  ∃ (ι : Module.Dual ℚ (linearCoker L) →ₗ[ℚ]
        Module.Dual ℚ (linearCoker (jointMap L A)))
    (ρ : Module.Dual ℚ (linearCoker (jointMap L A)) →ₗ[ℚ]
        (physicalHolonomy L A).dualAnnihilator),
    Function.Injective ι ∧
    Function.Surjective ρ ∧
    ρ.comp ι = 0 ∧
    LinearMap.range ι = LinearMap.ker ρ ∧
    (∀ φ : Module.Dual ℚ (linearCoker L),
      ∀ w : W, ∀ a : Z,
        ι φ ((LinearMap.range (jointMap L A)).mkQ (w, a)) =
          φ ((LinearMap.range L).mkQ w)) ∧
    (∀ ψ : Module.Dual ℚ (linearCoker (jointMap L A)),
      (ρ ψ).1 =
        (ψ.comp (LinearMap.range (jointMap L A)).mkQ).comp
          (LinearMap.inr ℚ W Z))

/-- R-5089.4: the response-only separator space and the exact freedom in the
scalar component of a joint annihilator. -/
def jointAnnihilator {C W Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z) :
    Set (Module.Dual ℚ W × Module.Dual ℚ Z) :=
  {q | q.1.comp L + q.2.comp A = 0}

def responseSeparators {C W Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z) :
    Set (Module.Dual ℚ Z) :=
  {η | ∃ φ : Module.Dual ℚ W, (φ, η) ∈ jointAnnihilator L A}

def claim54999 : Prop :=
  ∀ (C W Z : Type*)
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    [FiniteDimensional ℚ C] [FiniteDimensional ℚ W] [FiniteDimensional ℚ Z]
    (L : C →ₗ[ℚ] W) (A : C →ₗ[ℚ] Z),
    dualZeroScalarShortExact L A ∧
    responseSeparators L A =
        (physicalHolonomy L A).dualAnnihilator ∧
    (∀ (η : Module.Dual ℚ Z) (φ₁ φ₂ : Module.Dual ℚ W),
      (φ₁, η) ∈ jointAnnihilator L A →
      (φ₂, η) ∈ jointAnnihilator L A →
      φ₁ - φ₂ ∈ (LinearMap.range L).dualAnnihilator) ∧
    (∀ (η : Module.Dual ℚ Z) (φ : Module.Dual ℚ W)
        (δ : Module.Dual ℚ W),
      (φ, η) ∈ jointAnnihilator L A →
      δ ∈ (LinearMap.range L).dualAnnihilator →
      (φ + δ, η) ∈ jointAnnihilator L A) ∧
    (∀ a : Z,
      zeroScalarTarget L A a ≠ 0 ↔
        ∃ η ∈ (physicalHolonomy L A).dualAnnihilator, η a ≠ 0)

/-- R-5089.5: constrained response holonomy and the corresponding exact
sequence/rank and target formulas, with `F=(L,P)`. -/
def constrainedHolonomy {C W U Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup U] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ U] [Module ℚ Z]
    (L : C →ₗ[ℚ] W) (P : C →ₗ[ℚ] U) (A : C →ₗ[ℚ] Z) :
    Submodule ℚ Z :=
  physicalHolonomy (LinearMap.prod L P) A

def claim55000 : Prop :=
  ∀ (C W U Z : Type*)
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup U] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ U] [Module ℚ Z]
    [FiniteDimensional ℚ C] [FiniteDimensional ℚ W]
    [FiniteDimensional ℚ U] [FiniteDimensional ℚ Z]
    (L : C →ₗ[ℚ] W) (P : C →ₗ[ℚ] U) (A : C →ₗ[ℚ] Z),
    let F := LinearMap.prod L P
    let H := constrainedHolonomy L P A
    zeroScalarShortExact F A ∧
    (∀ a : Z,
      (LinearMap.range (F.prod A)).mkQ ((0, 0), a) = 0 ↔ a ∈ H) ∧
    Module.finrank ℚ H =
      Module.finrank ℚ (LinearMap.range (F.prod A)) -
        Module.finrank ℚ (LinearMap.range F)

end
end MathlibPlus.Open.ResearchHolonomy
