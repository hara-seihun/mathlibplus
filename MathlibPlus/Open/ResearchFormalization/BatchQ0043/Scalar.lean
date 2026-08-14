import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0043

noncomputable section
open scoped BigOperators

abbrev PosNat := {n : ℕ // 0 < n}
abbrev Ge2Nat := {n : ℕ // 1 < n}

def onePos : PosNat := ⟨1, by decide⟩

def ge2Pos (a : Ge2Nat) : PosNat :=
  ⟨a.1, Nat.lt_trans (by decide) a.2⟩

def ge2OfPos (a : PosNat) (h : a.1 ≠ 1) : Ge2Nat :=
  ⟨a.1,
    Nat.lt_of_le_of_ne
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt a.2))
      (by intro ha; exact h ha.symm)⟩

inductive BoundaryKind where
  | closed
  | open

def BoundaryVar := BoundaryKind × PosNat
abbrev ScalarPolynomial := MvPolynomial BoundaryVar ℚ

def deltaSource (a : PosNat) : ScalarPolynomial :=
  MvPolynomial.X (BoundaryKind.open, a) -
    MvPolynomial.X (BoundaryKind.closed, a)

def scalarRelation (a : Ge2Nat) : ScalarPolynomial :=
  deltaSource (ge2Pos a) - deltaSource onePos ^ a.1

def scalarRelations : Set ScalarPolynomial :=
  {p | ∃ a : Ge2Nat, p = scalarRelation a}

def scalarIdeal : Ideal ScalarPolynomial := Ideal.span scalarRelations

inductive SpecializationVar where
  | z
  | y (a : PosNat)

abbrev SpecializationPolynomial := MvPolynomial SpecializationVar ℚ

def scalarSpecialization : ScalarPolynomial →+* SpecializationPolynomial :=
  MvPolynomial.eval₂Hom (algebraMap ℚ SpecializationPolynomial) (fun v =>
    match v.1 with
    | BoundaryKind.closed =>
        MvPolynomial.X (SpecializationVar.y v.2) -
          MvPolynomial.X SpecializationVar.z ^ v.2.1
    | BoundaryKind.open =>
        MvPolynomial.X (SpecializationVar.y v.2))

inductive BaseVar where
  | delta
  | closed (a : Ge2Nat)

abbrev ScalarBase := MvPolynomial BaseVar ℚ
abbrev ScalarQuotientModel := Polynomial ScalarBase

def quotientDelta : ScalarQuotientModel :=
  Polynomial.C (MvPolynomial.X BaseVar.delta)

def quotientClosed (a : PosNat) : ScalarQuotientModel :=
  if h : a.1 = 1 then
    Polynomial.X
  else
    Polynomial.C (MvPolynomial.X (BaseVar.closed (ge2OfPos a h)))

def quotientOpen (a : PosNat) : ScalarQuotientModel :=
  quotientClosed a + quotientDelta ^ a.1

def quotientDerivative : ScalarQuotientModel →ₗ[ℚ] ScalarQuotientModel :=
  LinearMap.restrictScalars ℚ Polynomial.derivative

def quotientDerivativeKernel : Set ScalarQuotientModel :=
  {p | quotientDerivative p = 0}

def claim16119 : Prop :=
  RingHom.ker scalarSpecialization = scalarIdeal ∧
    (∃ e : (ScalarPolynomial ⧸ scalarIdeal) ≃ₐ[ℚ] ScalarQuotientModel,
      (∀ a : PosNat,
        e (Ideal.Quotient.mk scalarIdeal
            (MvPolynomial.X (BoundaryKind.closed, a))) =
          quotientClosed a) ∧
      (∀ a : PosNat,
        e (Ideal.Quotient.mk scalarIdeal
            (MvPolynomial.X (BoundaryKind.open, a))) =
          quotientOpen a)) ∧
    quotientDerivativeKernel = Set.range (fun b : ScalarBase => Polynomial.C b)

def primitiveTranslate (α β : PosNat → ℚ) :
    ScalarPolynomial →+* ScalarPolynomial :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ScalarPolynomial) (fun v =>
    match v.1 with
    | BoundaryKind.closed =>
        MvPolynomial.X (BoundaryKind.closed, v.2) +
          MvPolynomial.C (α v.2)
    | BoundaryKind.open =>
        MvPolynomial.X (BoundaryKind.open, v.2) +
          MvPolynomial.C (β v.2))

def descendsThroughScalarQuotient
    (T : ScalarPolynomial →+* ScalarPolynomial) : Prop :=
  Ideal.map T scalarIdeal ≤ scalarIdeal

def baseTranslate (α : PosNat → ℚ) : ScalarBase →+* ScalarBase :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ScalarBase) (fun v =>
    match v with
    | BaseVar.delta => MvPolynomial.X BaseVar.delta
    | BaseVar.closed a =>
        MvPolynomial.X (BaseVar.closed a) +
          MvPolynomial.C (α (ge2Pos a)))

def baseTranslateToQuotient (α : PosNat → ℚ) :
    ScalarBase →+* ScalarQuotientModel :=
  (algebraMap ScalarBase ScalarQuotientModel).comp (baseTranslate α)

def quotientTranslate (α : PosNat → ℚ) :
    ScalarQuotientModel →+* ScalarQuotientModel :=
  Polynomial.eval₂RingHom (baseTranslateToQuotient α)
    ((Polynomial.X : ScalarQuotientModel) +
      (Polynomial.C (MvPolynomial.C (α onePos)) : ScalarQuotientModel))

def quotientTranslationFixesDelta (α : PosNat → ℚ) : Prop :=
  quotientTranslate α quotientDelta = quotientDelta

def quotientTranslationCommutesWithDerivative (α : PosNat → ℚ) : Prop :=
  ∀ p : ScalarQuotientModel,
    quotientDerivative (quotientTranslate α p) =
      quotientTranslate α (quotientDerivative p)

def quotientTranslationPreservesDerivativeKernel (α : PosNat → ℚ) : Prop :=
  ∀ p : ScalarQuotientModel,
    quotientDerivative p = 0 →
      quotientDerivative (quotientTranslate α p) = 0

def claim16120 : Prop :=
  ∀ α β : PosNat → ℚ,
    (descendsThroughScalarQuotient (primitiveTranslate α β) ↔
      ∀ a : PosNat, α a = β a) ∧
    (descendsThroughScalarQuotient (primitiveTranslate α β) →
      quotientTranslationFixesDelta α ∧
      quotientTranslationCommutesWithDerivative α ∧
      quotientTranslationPreservesDerivativeKernel α) ∧
    ((∃ a : PosNat, α a ≠ β a) →
      ¬ descendsThroughScalarQuotient (primitiveTranslate α β))

inductive XVar where
  | x (a : PosNat)

abbrev XCoefficient := MvPolynomial XVar ℚ
abbrev ClosurePolynomial := Polynomial XCoefficient

def baseToPreclosure : ScalarBase →+* ClosurePolynomial :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ClosurePolynomial) (fun v =>
    match v with
    | BaseVar.delta => Polynomial.X
    | BaseVar.closed a =>
        Polynomial.C (MvPolynomial.X (XVar.x (ge2Pos a))))

def preclosure : ScalarQuotientModel →+* ClosurePolynomial :=
  Polynomial.eval₂RingHom baseToPreclosure
    (Polynomial.C (MvPolynomial.X (XVar.x onePos)))

def lambdaZ (H : ClosurePolynomial) : ClosurePolynomial :=
  Finset.sum H.support (fun k =>
    (Polynomial.C (MvPolynomial.X (XVar.x ⟨k + 1, Nat.succ_pos k⟩)) +
        Polynomial.X ^ (k + 1)) * Polynomial.C (H.coeff k))

def claim16121 : Prop :=
  Function.Injective preclosure ∧
    Function.Injective lambdaZ ∧
    Function.Injective (lambdaZ ∘ preclosure) ∧
    (∀ (H : ClosurePolynomial) (k : ℕ),
      H.coeff k = (lambdaZ H).coeff (k + 1))


end
end MathlibPlus.Open.ResearchFormalization.BatchQ0043
