import MathlibPlus.Open.ResearchFormalization.BatchVoltage

namespace MathlibPlus.Open.ResearchFormalization.ScalarCubicRowShadow

open MathlibPlus.Open.ResearchFormalization.BatchVoltage

noncomputable section

abbrev C3 := Three

/-- The quotient-identity fibre map in the displayed semidirect coordinates. -/
def quotientIdentityMap {M : Type*} [AddCommGroup M]
    (F : C3 → Equiv.Perm M) (x : E M) : E M :=
  (F x.2 x.1, x.2)

/-- A quotient-identity isomorphism of the directed Cayley relations. -/
def quotientIdentityCayleyIsomorphism {M : Type*} [AddCommGroup M]
    (theta : M ≃+ M) (S T : Set (E M))
    (F : C3 → Equiv.Perm M) : Prop :=
  Function.Bijective (quotientIdentityMap F) ∧
    ∀ x y : E M,
      voltageAdj theta S x y ↔
        voltageAdj theta T
          (quotientIdentityMap F x) (quotientIdentityMap F y)

/-- The row sections of a connection set. -/
def scalarCubicSection {M : Type*}
    (S : Set (E M)) (i : C3) : Set M :=
  {w | (w, i) ∈ S}

/-- The constants and the displayed scalar-cubic cocycle. -/
def rowOrigin {M : Type*} [AddCommGroup M]
    (F : C3 → Equiv.Perm M) (i : C3) : M :=
  F i 0

def scalarCubicZ {M : Type*} [AddCommGroup M]
    (theta : M ≃+ M) (F : C3 → Equiv.Perm M) (i : C3) : M :=
  if i = 0 then 0
  else if i = 1 then rowOrigin F 1
  else rowOrigin F 1 + theta (rowOrigin F 1)

def scalarCubicAlpha {M : Type*} [AddCommGroup M]
    (theta : M ≃+ M) (F : C3 → Equiv.Perm M) (x : E M) : E M :=
  (x.1 + scalarCubicZ theta F x.2, x.2)

/-- A multiplicative bijection for the displayed semidirect-product law. -/
def scalarCubicGroupAutomorphism {M : Type*} [AddCommGroup M]
    (theta : M ≃+ M) (F : C3 → Equiv.Perm M) : Prop :=
  Function.Bijective (scalarCubicAlpha theta F) ∧
    ∀ x y : E M,
      scalarCubicAlpha theta F (semidirectMul theta x y) =
        semidirectMul theta
          (scalarCubicAlpha theta F x) (scalarCubicAlpha theta F y)

/-- Claim 61219: inverse-closed quotient-identity scalar-cubic row shadow. -/
def inverseClosedQuotientIdentityScalarCubicRowShadowClaim61219 : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Finite M]
    (theta : M ≃+ M),
    fixedPointFree theta →
    orderThree theta →
    ∀ (S T : Set (E M)),
      voltageInverseClosed theta S →
      voltageInverseClosed theta T →
      ∀ (F : C3 → Equiv.Perm M),
        F 0 = Equiv.refl M →
        quotientIdentityCayleyIsomorphism theta S T F →
          let c : C3 → M := rowOrigin F
          let z : C3 → M := scalarCubicZ theta F
          let alpha : E M → E M := scalarCubicAlpha theta F
          scalarCubicGroupAutomorphism theta F ∧
            c 0 = 0 ∧
            z 0 = 0 ∧
            z 1 = c 1 ∧
            z 2 = c 1 + theta (c 1) ∧
            z 2 = -(thetaPower theta 2) (c 1) ∧
            (∀ i j : C3,
              z (i + j) = z i + (thetaPower theta i) (z j)) ∧
            Set.image alpha S = T

end

end MathlibPlus.Open.ResearchFormalization.ScalarCubicRowShadow
