import Mathlib
import Mathlib.Algebra.DualNumber

namespace MathlibPlus.Open.ResearchFormalization.R3738Claim50252

noncomputable section

abbrev CoefficientRing (R : Type*) [CommSemiring R] := MvPolynomial ℕ R
abbrev RootedPolynomial (R : Type*) [CommSemiring R] :=
  Polynomial (CoefficientRing R)

def dualCoefficientSpecialization {R : Type*} [CommRing R]
    (t u r v : R) : CoefficientRing R →+* DualNumber R :=
  MvPolynomial.eval₂Hom (algebraMap R (DualNumber R))
    (fun i =>
      if i = 0 then TrivSqZeroExt.inl t
      else
        TrivSqZeroExt.inl (u * r ^ i) +
          DualNumber.eps * TrivSqZeroExt.inl (v ^ i))

def dualizedRootedPolynomial {R : Type*} [CommRing R]
    (t u r v : R) (E : RootedPolynomial R) :
    Polynomial (DualNumber R) :=
  Polynomial.map (dualCoefficientSpecialization t u r v) E

def dualEvaluation {R : Type*} [CommRing R]
    (t u r v s : R) (E : RootedPolynomial R) : DualNumber R :=
  Polynomial.eval₂ (RingHom.id (DualNumber R))
    (TrivSqZeroExt.inl s) (dualizedRootedPolynomial t u r v E)

def baseSpecialization {R : Type*} [CommRing R]
    (t u r v s : R) (E : RootedPolynomial R) : R :=
  (dualEvaluation t u r v s E).1

def normalSpecialization {R : Type*} [CommRing R]
    (t u r v s : R) (E : RootedPolynomial R) : R :=
  (dualEvaluation t u r v s E).2

def baseConstantSpecialization {R : Type*} [CommRing R]
    (t u r v : R) (E : RootedPolynomial R) : R :=
  (dualCoefficientSpecialization t u r v (E.coeff 0)).1

def normalConstantSpecialization {R : Type*} [CommRing R]
    (t u r v : R) (E : RootedPolynomial R) : R :=
  (dualCoefficientSpecialization t u r v (E.coeff 0)).2

/-- The two base equations supplied by the dual-number selector formulas. -/
def baseSelectorValues {R : Type*} [CommRing R]
    (t u r v : R) (E : RootedPolynomial R) : R × R :=
  (u * baseSpecialization t u r v r E +
      (t - u) * baseConstantSpecialization t u r v E,
    u * r * baseSpecialization t u r v r E)

def baseSelectorKernel {R : Type*} [CommRing R]
    (t u r v : R) (E : RootedPolynomial R) : Prop :=
  baseSelectorValues t u r v E = (0, 0)

/-- Claim 50252: the nonzero factors in the S1 base equations and the domain
property force both the one-exponential value and the constant-marker value to
vanish. -/
def claim50252 : Prop :=
  ∀ (R : Type*) [CommRing R] [IsDomain R]
    (E : RootedPolynomial R) (t u r v : R),
    u ≠ 0 → r ≠ 0 → t - u ≠ 0 →
      baseSelectorKernel t u r v E →
        baseSpecialization t u r v r E = 0 ∧
          baseConstantSpecialization t u r v E = 0

end

end MathlibPlus.Open.ResearchFormalization.R3738Claim50252
