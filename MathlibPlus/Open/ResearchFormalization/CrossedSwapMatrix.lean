import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev GenericScalar := FractionRing (MvPolynomial (Fin 4) ℚ)

noncomputable def genericVariable (i : Fin 4) : GenericScalar :=
  algebraMap (MvPolynomial (Fin 4) ℚ) GenericScalar (MvPolynomial.X i)

noncomputable abbrev a : GenericScalar := genericVariable 0
noncomputable abbrev b : GenericScalar := genericVariable 1
noncomputable abbrev c : GenericScalar := genericVariable 2
noncomputable abbrev d : GenericScalar := genericVariable 3

noncomputable def halfTermMatrix : Matrix (Fin 4) (Fin 4) GenericScalar :=
  !![b - c, b - d, 0, 0;
     0, 0, a - c, a - d;
     a - d, 0, b - d, 0;
     0, a - c, 0, b - c]

noncomputable def halfTermKernelVector : Fin 4 → GenericScalar :=
  ![b - d, c - b, d - a, a - c]

def minorRows : Fin 3 → Fin 4 := ![2, 1, 3]

def minorColumns : Fin 3 → Fin 4 := ![1, 2, 3]

noncomputable def displayedMinor : Matrix (Fin 3) (Fin 3) GenericScalar :=
  fun i j => halfTermMatrix (minorRows i) (minorColumns j)

def crossedSwapHalfTermRankAndMinor : Prop :=
  Matrix.rank halfTermMatrix = 3 ∧
    Matrix.det displayedMinor = (a - c) * (a - d) * (b - d)

def crossedSwapGenericKernel : Prop :=
  Matrix.mulVec halfTermMatrix halfTermKernelVector = 0 ∧
    ∀ x : Fin 4 → GenericScalar,
      Matrix.mulVec halfTermMatrix x = 0 →
        ∃ t : GenericScalar, x = t • halfTermKernelVector

end MathlibPlus.Open.ResearchFormalization
