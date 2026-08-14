import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0695

noncomputable section

abbrev PositiveIndex := {a : ℕ // 0 < a}

/-- The polynomial ring with one `c_a` and one `o_a` for every positive size. -/
abbrev PrimitiveScalarPolynomial :=
  MvPolynomial (Sum PositiveIndex PositiveIndex) ℚ

/-- The target polynomial ring with variables `y_a` and `z`. -/
abbrev ShiftedScalarPolynomial :=
  MvPolynomial (Option PositiveIndex) ℚ

def cVar (a : PositiveIndex) : PrimitiveScalarPolynomial :=
  MvPolynomial.X (Sum.inl a)

def oVar (a : PositiveIndex) : PrimitiveScalarPolynomial :=
  MvPolynomial.X (Sum.inr a)

def deltaVar (a : PositiveIndex) : PrimitiveScalarPolynomial :=
  oVar a - cVar a

def yVar (a : PositiveIndex) : ShiftedScalarPolynomial :=
  MvPolynomial.X (some a)

def zVar : ShiftedScalarPolynomial :=
  MvPolynomial.X none

/--
The primitive scalar boundary algebra and its generators.  The two summands of
`Sum PositiveIndex PositiveIndex` distinguish `c_a` from `o_a`, and `deltaVar`
is the stated difference.
-/
def primitiveScalarBoundaryAlgebra : Prop :=
  ∀ a : PositiveIndex,
    cVar a = MvPolynomial.X (Sum.inl a) ∧
      oVar a = MvPolynomial.X (Sum.inr a) ∧
        deltaVar a = oVar a - cVar a

/-- The shifted rooted-factor specialization on the two families of generators. -/
def shiftedSpecialization : PrimitiveScalarPolynomial →+* ShiftedScalarPolynomial :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ShiftedScalarPolynomial)
    (fun i : Sum PositiveIndex PositiveIndex =>
      match i with
      | Sum.inl a => yVar a - zVar ^ (a : ℕ)
      | Sum.inr a => yVar a)

/--
The specialization sends `c_a` to `y_a-z^a`, `o_a` to `y_a`, and hence the
primitive difference `delta_a` to `z^a`.
-/
def shiftedScalarRootedFactorSpecialization : Prop :=
  (∀ a : PositiveIndex,
      shiftedSpecialization (cVar a) = yVar a - zVar ^ (a : ℕ)) ∧
    (∀ a : PositiveIndex, shiftedSpecialization (oVar a) = yVar a) ∧
      (∀ a : PositiveIndex,
        shiftedSpecialization (deltaVar a) = zVar ^ (a : ℕ))

end

end MathlibPlus.Open.ResearchFormalization.R0695
