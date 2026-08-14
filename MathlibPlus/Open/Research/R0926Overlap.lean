import Mathlib

namespace MathlibPlus.Open.Research.R0926

noncomputable section

variable {K U L R O : Type*}
variable [Field K]
variable [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable [AddCommGroup L] [Module K L]
variable [AddCommGroup R] [Module K R]
variable [AddCommGroup O] [Module K O]

/-- The overlap compatibility map `(l,r) ↦ resL l - resR r`. -/
def agreeMap
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O) :
    (L × R) →ₗ[K] O :=
  resL.comp (LinearMap.fst K L R) -
    resR.comp (LinearMap.snd K L R)

/-- Coefficient pairs whose two local features agree on the overlap. -/
def compatibleCoefficientPairs
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O) :
    Submodule K (U × U) :=
  LinearMap.ker (agreeMap (resL.comp phiL) (resR.comp phiR))

/-- The map sending two coefficient vectors to their two local sections. -/
def pairFeatureMap
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R) :
    (U × U) →ₗ[K] (L × R) :=
  (phiL.comp (LinearMap.fst K U U)).prod
    (phiR.comp (LinearMap.snd K U U))

/-- The submodule `P` of compatible local feature sections. It is the image
of the compatible coefficient pairs, rather than an unrestricted product of
local target spaces. -/
def compatibleSections
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O) :
    Submodule K (L × R) :=
  Submodule.map (pairFeatureMap phiL phiR)
    (compatibleCoefficientPairs phiL phiR resL resR)

/-- The diagonal map of one global coefficient vector. -/
def diagonalSections
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R) :
    U →ₗ[K] (L × R) :=
  phiL.prod phiR

/-- The denominator `D` viewed as a submodule of `P`; under the displayed
restriction equalities the diagonal range is contained in `P`. -/
def diagonalRangeInCompatible
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O) :
    Submodule K (compatibleSections phiL phiR resL resR) :=
  Submodule.comap
    (Submodule.subtype (compatibleSections phiL phiR resL resR))
    (LinearMap.range (diagonalSections phiL phiR))

/-- The left-hand defect quotient `P / D`. -/
abbrev overlapQuotient
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (phiO : U →ₗ[K] O)
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O)
    (hL : resL.comp phiL = phiO)
    (hR : resR.comp phiR = phiO) :=
  (↥(compatibleSections phiL phiR resL resR)) ⧸
    diagonalRangeInCompatible phiL phiR resL resR

/-- The denominator of the kernel quotient, represented as a submodule of
`ker phiO`; under the restriction equalities it is the kernel join. -/
def kernelJoinInOverlap
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (phiO : U →ₗ[K] O) :
    Submodule K (LinearMap.ker phiO) :=
  Submodule.comap
    (Submodule.subtype (LinearMap.ker phiO))
    (LinearMap.ker phiL ⊔ LinearMap.ker phiR)

/-- The right-hand quotient `ker phiO / (ker phiL ⊔ ker phiR)`. -/
abbrev kernelQuotient
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (phiO : U →ₗ[K] O)
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O)
    (hL : resL.comp phiL = phiO)
    (hR : resR.comp phiR = phiO) :=
  (↥(LinearMap.ker phiO)) ⧸
    kernelJoinInOverlap phiL phiR phiO

/-- The quotient equivalence and its prescribed normal form. -/
def overlapKernelQuotientEquivalence
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (phiO : U →ₗ[K] O)
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O)
    (hL : resL.comp phiL = phiO)
    (hR : resR.comp phiR = phiO) : Prop :=
  ∃ e : overlapQuotient phiL phiR phiO resL resR hL hR ≃ₗ[K]
      kernelQuotient phiL phiR phiO resL resR hL hR,
    ∀ (a b : U) (hab : resL (phiL a) = resR (phiR b)),
      ∃ p : compatibleSections phiL phiR resL resR,
        ∃ k : LinearMap.ker phiO,
          p.1 = (phiL a, phiR b) ∧
          k.1 = a - b ∧
          e (Submodule.Quotient.mk p) = Submodule.Quotient.mk k

/-- Rank of a linear feature map, as the dimension of its range. -/
def rankK {W : Type*} [AddCommGroup W] [Module K W]
    (f : U →ₗ[K] W) : ℕ :=
  Module.finrank K (LinearMap.range f)

/-- The natural-dimension formula for the overlap defect. `_hGlobal` records
that the global map is the feature map on the union of the two windows. -/
def dimensionFormula
    {W : Type*} [AddCommGroup W] [Module K W]
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (phiO : U →ₗ[K] O)
    (phiV : U →ₗ[K] W)
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O)
    (hL : resL.comp phiL = phiO)
    (hR : resR.comp phiR = phiO)
    (_hGlobal : LinearMap.ker phiV = LinearMap.ker phiL ⊓ LinearMap.ker phiR) : Prop :=
  Module.finrank K (overlapQuotient phiL phiR phiO resL resR hL hR) =
    rankK phiL + rankK phiR - rankK phiO - rankK phiV

/-- Compatible local sections descend exactly when the defect quotient is
trivial. -/
def descentCriterion
    (phiL : U →ₗ[K] L)
    (phiR : U →ₗ[K] R)
    (phiO : U →ₗ[K] O)
    (resL : L →ₗ[K] O)
    (resR : R →ₗ[K] O)
    (hL : resL.comp phiL = phiO)
    (hR : resR.comp phiR = phiO) : Prop :=
  Subsingleton (overlapQuotient phiL phiR phiO resL resR hL hR) ↔
    LinearMap.ker phiO = LinearMap.ker phiL ⊔ LinearMap.ker phiR

end

end MathlibPlus.Open.Research.R0926
