import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R3607

abbrev C1 := Fin 2 → ℚ
abbrev C2 := Fin 2 → ℚ
abbrev C3 := Fin 1 → ℚ

/-- The ordered degree-one basis `(p,w)`. -/
def pBasis : C1 := Pi.single 0 1

def wBasis : C1 := Pi.single 1 1

/-- The ordered degree-two basis `(m,a)`. -/
def mBasis : C2 := Pi.single 0 1

def aBasis : C2 := Pi.single 1 1

/-- The ordered degree-three basis `(r)`. -/
def rBasis : C3 := Pi.single 0 1

def d1UMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 0, 0]

def d1AMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

def d2Matrix : Matrix (Fin 1) (Fin 2) ℚ := !![1, 0]

def d1U : C1 →ₗ[ℚ] C2 := Matrix.toLin' d1UMatrix

def d1A : C1 →ₗ[ℚ] C2 := Matrix.toLin' d1AMatrix

def d2 : C2 →ₗ[ℚ] C3 := Matrix.toLin' d2Matrix

/-- The second cohomology dimension in this three-step complex, written in
coordinates as the kernel dimension minus the incidence-range dimension. -/
def secondCohomologyDimension (d1 : C1 →ₗ[ℚ] C2)
    (d₂ : C2 →ₗ[ℚ] C3) : ℕ :=
  Module.finrank ℚ (LinearMap.ker d₂) -
    Module.finrank ℚ (LinearMap.range d1)

/-- Claim 49339: the two support-preserving incidence choices have second
cohomology dimensions one and zero, respectively. -/
def claim49339 : Prop :=
  d2.comp d1U = 0 ∧
    d2.comp d1A = 0 ∧
    LinearMap.ker d2 = Submodule.span ℚ ({aBasis} : Set C2) ∧
    LinearMap.range d1U = (⊥ : Submodule ℚ C2) ∧
    LinearMap.range d1A = Submodule.span ℚ ({aBasis} : Set C2) ∧
    secondCohomologyDimension d1U d2 = 1 ∧
    secondCohomologyDimension d1A d2 = 0 ∧
    Module.finrank ℚ (LinearMap.ker d2) -
        Module.finrank ℚ (LinearMap.range d1U) = 1 ∧
    Module.finrank ℚ (LinearMap.ker d2) -
        Module.finrank ℚ (LinearMap.range d1A) = 0

/-- The finite five-cell carrier, in the order `(p,w,m,a,r)`. -/
abbrev RelativeCells49342 := Fin 5

def pCell49342 : RelativeCells49342 := 0

def wCell49342 : RelativeCells49342 := 1

def mCell49342 : RelativeCells49342 := 2

def aCell49342 : RelativeCells49342 := 3

def rCell49342 : RelativeCells49342 := 4

def relativeCellLabels49342 : Set RelativeCells49342 :=
  {pCell49342, wCell49342, mCell49342, aCell49342, rCell49342}

/-- The cellular degree-two boundary matrices whose transposes are the two
incidence coboundaries. -/
def cellularBoundary2UMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.transpose d1UMatrix

def cellularBoundary2AMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.transpose d1AMatrix

def cellularBoundary2U : C2 →ₗ[ℚ] C1 :=
  Matrix.toLin' cellularBoundary2UMatrix

def cellularBoundary2A : C2 →ₗ[ℚ] C1 :=
  Matrix.toLin' cellularBoundary2AMatrix

def cellularCoboundary2U : C1 →ₗ[ℚ] C2 :=
  Matrix.toLin' (Matrix.transpose cellularBoundary2UMatrix)

def cellularCoboundary2A : C1 →ₗ[ℚ] C2 :=
  Matrix.toLin' (Matrix.transpose cellularBoundary2AMatrix)

def cellularBoundary3Matrix : Matrix (Fin 2) (Fin 1) ℚ := !![1; 0]

def cellularBoundary3 : C3 →ₗ[ℚ] C2 :=
  Matrix.toLin' cellularBoundary3Matrix

def cellularCoboundary3 : C2 →ₗ[ℚ] C3 :=
  Matrix.toLin' (Matrix.transpose cellularBoundary3Matrix)

/-- Claim 49342: on the finite five-cell carrier ordered by the displayed
bases as `(p,w,m,a,r)`, the degree-three boundary is `m`, the two possible
attaching boundaries of `a` are zero and `p`, and their transposed cellular
coboundaries are the two displayed incidence maps. -/
def claim49342 : Prop :=
  Fintype.card RelativeCells49342 = 5 ∧
    relativeCellLabels49342 = Set.univ ∧
    cellularBoundary3 rBasis = mBasis ∧
    cellularBoundary2U aBasis = 0 ∧
    cellularBoundary2A aBasis = pBasis ∧
    cellularCoboundary2U = d1U ∧
    cellularCoboundary2A = d1A ∧
    cellularCoboundary3 = d2 ∧
    d2.comp d1U = 0 ∧
    d2.comp d1A = 0

end MathlibPlus.Open.ResearchFormalization.R3607
