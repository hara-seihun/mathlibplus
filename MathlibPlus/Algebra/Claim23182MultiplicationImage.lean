import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Algebra.Claim23182

open MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev RelativeTensor23182 (B : Subalgebra ℚ RootRing) :=
  TensorProduct B RootRing RootRing

/-- The class of a pure tensor in the diagonal relative tensor product. -/
def relativeTensorTmul23182
    (B : Subalgebra ℚ RootRing) (a a' : RootRing) : RelativeTensor23182 B :=
  TensorProduct.tmul B a a'

/-- The scalar rooted-factor test elements. -/
def scalarS23182 : RootRing := rootClosure (1 : RootRing)
def scalarE23182 : RootRing := rootClosure scalarS23182
def scalarP23182 : RootRing := rootClosure scalarE23182
def scalarC23182 : RootRing := rootClosure (scalarS23182 ^ 2)
def scalarQ23182 : RootRing := scalarE23182 - scalarS23182 ^ 2

/-- The balanced defect from the scalar operated relation. -/
def relativeDefect23182
    (B : Subalgebra ℚ RootRing) : RelativeTensor23182 B :=
  relativeTensorTmul23182 B scalarS23182 (scalarC23182 - scalarS23182 * scalarE23182) -
    relativeTensorTmul23182 B scalarQ23182 scalarQ23182 +
    relativeTensorTmul23182 B (scalarP23182 - scalarC23182) scalarS23182

/-- A linear map on the relative tensor product is the descended ordinary
multiplication when it has the prescribed value on every pure tensor. -/
def isMultiplicationMap23182
    (B : Subalgebra ℚ RootRing)
    (m : RelativeTensor23182 B →ₗ[B] RootRing) : Prop :=
  ∀ a a' : RootRing,
    m (relativeTensorTmul23182 B a a') = a * a'

/-- The ambient diagonal-central base condition. -/
def diagonalCentralBase23182 (B : Subalgebra ℚ RootRing) : Prop :=
  B ≤ scalarRootedFactorAlgebra ∧
    ∀ b : RootRing, b ∈ B → ∀ a : RootRing, b * a = a * b

/-- The multiplication image of the balanced defect, with the common value
made independent of the diagonal base. -/
def multiplicationImageOfDefect_claim23182 : Prop :=
  ∀ B : Subalgebra ℚ RootRing,
    diagonalCentralBase23182 B →
    ∃! m : RelativeTensor23182 B →ₗ[B] RootRing,
      isMultiplicationMap23182 B m ∧
        m (relativeDefect23182 B) =
          scalarS23182 * (scalarC23182 - scalarS23182 * scalarE23182) -
            scalarQ23182 ^ 2 +
            (scalarP23182 - scalarC23182) * scalarS23182 ∧
        scalarS23182 * (scalarC23182 - scalarS23182 * scalarE23182) -
            scalarQ23182 ^ 2 +
            (scalarP23182 - scalarC23182) * scalarS23182 =
          scalarS23182 * (scalarP23182 - scalarS23182 * scalarE23182) -
            scalarQ23182 ^ 2

end

end MathlibPlus.Algebra.Claim23182
