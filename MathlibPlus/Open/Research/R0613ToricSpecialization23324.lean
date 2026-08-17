import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactorR0613

open scoped BigOperators

namespace MathlibPlus.Open.Research.R0613ToricSpecialization23324

noncomputable section

abbrev PositiveIndex := ℕ+
abbrev RootRing := Polynomial (MvPolynomial PositiveIndex ℚ)
abbrev ToricRing := MvPolynomial (Fin 2) ℚ
abbrev TriangularIndex := {k : PositiveIndex // 2 ≤ (k : ℕ)}

def rootZ : RootRing := Polynomial.X

def rootX (k : PositiveIndex) : RootRing :=
  Polynomial.C (MvPolynomial.X k)

def toricU : ToricRing := MvPolynomial.X 0

def toricV : ToricRing := MvPolynomial.X 1

def toricCoefficientMap : MvPolynomial PositiveIndex ℚ →+* ToricRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ToricRing)
    (fun k => toricU * toricV ^ (k : ℕ))

def toricSpecialization : RootRing →ₐ[ℚ] ToricRing :=
  RingHom.toRatAlgHom
    (Polynomial.eval₂RingHom toricCoefficientMap toricV)

def triangularDifference (k : TriangularIndex) : RootRing :=
  rootX k.1 - rootZ ^ ((k : ℕ) - 1) * rootX (1 : PositiveIndex)

def coordinateGenerators : Set RootRing :=
  insert rootZ (insert (rootX (1 : PositiveIndex))
    (Set.range triangularDifference))

def coordinateSubalgebra : Subalgebra ℚ RootRing :=
  Algebra.adjoin ℚ coordinateGenerators

def kernelIdeal : Ideal RootRing :=
  RingHom.ker toricSpecialization.toRingHom

/-- Claim 23324: the positive-index toric specialization sends `z` to `v`
and `x_k` to `u v^k`; the triangular differences generate its full kernel,
and `z,x₁,e₂,e₃,…` generate the ambient positive-index polynomial ring. -/
def claim23324_fullToricSpecializationAndAmbientKernel : Prop :=
  toricSpecialization rootZ = toricV ∧
    (∀ k : PositiveIndex,
      toricSpecialization (rootX k) = toricU * toricV ^ (k : ℕ)) ∧
      kernelIdeal = Ideal.span (Set.range triangularDifference) ∧
        coordinateSubalgebra = ⊤

end

end MathlibPlus.Open.Research.R0613ToricSpecialization23324
