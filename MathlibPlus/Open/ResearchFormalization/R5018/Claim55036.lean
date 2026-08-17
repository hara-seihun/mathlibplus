import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5018.Claim55036

universe uC0 uC1 uW0 uW1 uZ

variable {C0 : Type uC0} {C1 : Type uC1}
  {W0 : Type uW0} {W1 : Type uW1} {Z : Type uZ}
variable [AddCommGroup C0] [AddCommGroup C1]
  [AddCommGroup W0] [AddCommGroup W1] [AddCommGroup Z]
variable [Module ℚ C0] [Module ℚ C1]
  [Module ℚ W0] [Module ℚ W1] [Module ℚ Z]
variable [FiniteDimensional ℚ C0] [FiniteDimensional ℚ C1]
  [FiniteDimensional ℚ W0] [FiniteDimensional ℚ W1]
  [FiniteDimensional ℚ Z]

/-- Scalar compatibility of an admissible physical map. -/
def scalarCompatible
    (L0 : C0 →ₗ[ℚ] W0) (L1 : C1 →ₗ[ℚ] W1)
    (S : W0 →ₗ[ℚ] W1) (E : C0 →ₗ[ℚ] C1) : Prop :=
  L1.comp E = S.comp L0

/-- The response error of a physical lift. -/
def responseError
    (A0 : C0 →ₗ[ℚ] Z) (A1 : C1 →ₗ[ℚ] Z)
    (E : C0 →ₗ[ℚ] C1) : C0 →ₗ[ℚ] Z :=
  A1.comp E - A0

/-- A scalar-null admissible deformation. -/
def scalarNullPhysical
    (P : Submodule ℚ (C0 →ₗ[ℚ] C1))
    (L1 : C1 →ₗ[ℚ] W1) (K : C0 →ₗ[ℚ] C1) : Prop :=
  K ∈ P ∧ L1.comp K = 0

/-- Equality in the response quotient modulo scalar coboundaries and
scalar-null physical deformations. -/
def responseClassEquivalent
    (P : Submodule ℚ (C0 →ₗ[ℚ] C1))
    (L0 : C0 →ₗ[ℚ] W0) (L1 : C1 →ₗ[ℚ] W1)
    (A0 : C0 →ₗ[ℚ] Z) (A1 : C1 →ₗ[ℚ] Z)
    (E E' : C0 →ₗ[ℚ] C1) : Prop :=
  ∃ (Ψ : W0 →ₗ[ℚ] Z) (K : C0 →ₗ[ℚ] C1),
    K ∈ P ∧ L1.comp K = 0 ∧
      responseError A0 A1 E - responseError A0 A1 E' =
        Ψ.comp L0 + A1.comp K

/-- Claim 55036: independent scalar-coboundary recentering changes each
scalar-compatible lift's error by the displayed coboundary, leaves every
scalar-null response deformation unchanged, and preserves the entire
all-lifts response quotient relation. -/
def claim55036
    (P : Submodule ℚ (C0 →ₗ[ℚ] C1))
    (L0 : C0 →ₗ[ℚ] W0) (L1 : C1 →ₗ[ℚ] W1)
    (S : W0 →ₗ[ℚ] W1)
    (A0 : C0 →ₗ[ℚ] Z) (A1 : C1 →ₗ[ℚ] Z)
    (Φ0 : W0 →ₗ[ℚ] Z) (Φ1 : W1 →ₗ[ℚ] Z) : Prop :=
  (∀ E : C0 →ₗ[ℚ] C1, E ∈ P →
    scalarCompatible L0 L1 S E →
      responseError (A0 + Φ0.comp L0) (A1 + Φ1.comp L1) E =
        responseError A0 A1 E + (Φ1.comp S - Φ0).comp L0) ∧
  (∀ K : C0 →ₗ[ℚ] C1, scalarNullPhysical P L1 K →
    (A1 + Φ1.comp L1).comp K = A1.comp K) ∧
  (∀ E E' : C0 →ₗ[ℚ] C1,
    E ∈ P → E' ∈ P →
      scalarCompatible L0 L1 S E →
      scalarCompatible L0 L1 S E' →
        (responseClassEquivalent P L0 L1 A0 A1 E E' ↔
          responseClassEquivalent P L0 L1
            (A0 + Φ0.comp L0) (A1 + Φ1.comp L1) E E'))

end MathlibPlus.Open.ResearchFormalization.R5018.Claim55036
