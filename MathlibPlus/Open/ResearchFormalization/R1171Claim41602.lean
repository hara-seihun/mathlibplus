import Mathlib
import MathlibPlus.Open.GroupTheory.FiberShearClaim41596
import MathlibPlus.Open.ResearchFormalization.R1171Claim41590

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41602

open MathlibPlus.Open.ResearchFormalization.R1171Claim41590

noncomputable section

abbrev Scalar := ZMod 5
abbrev Fibre := Fin 4 → Scalar
abbrev Omega := Scalar × Fibre
abbrev Permutation := Equiv.Perm Omega
abbrev FunctionSpace := Fibre → Scalar

/-- The translation copy used in the fibre-shear construction. -/
def translationCopy : Subgroup (Permutation) :=
  Subgroup.closure
    (Set.range (fun a : Omega => Equiv.addRight a))

/-- The displayed fibre shear, expressed as a pointwise condition on its
permutation carrier. -/
def fibreShearFormula (f : Fibre → Scalar) (q : Permutation) : Prop :=
  ∀ z : Scalar, ∀ v : Fibre,
    q (z, v) = (z + f v, v)

/-- The target copy obtained via the inverse displayed shear. -/
def targetCopy (q : Permutation) : Subgroup (Permutation) :=
  translationCopy.map (MulAut.conj q⁻¹)

/-- The finite-difference module from the exact source construction. -/
def fibreDifference (f : Fibre → Scalar) (u v : Fibre) : Scalar :=
  f (v + u) - f v

def fibreTranslate (w : Fibre) (g : FunctionSpace) : FunctionSpace :=
  fun v => g (v + w)

def constantOne : FunctionSpace :=
  fun _ => 1

def derivativeModule (f : Fibre → Scalar) : Submodule Scalar FunctionSpace :=
  Submodule.span Scalar
    ({constantOne} ∪
      {g | ∃ u w : Fibre,
        g = fibreTranslate w (fibreDifference f u)})

/-- The fibre on which all derivative-module functions are constant. -/
def shearZ (f : Fibre → Scalar) : Set Fibre :=
  {v | ∀ m : derivativeModule f,
    m.1 v = m.1 (0 : Fibre)}

def isSubspace (Z : Set Fibre) : Prop :=
  ∃ W : Submodule Scalar Fibre, (W : Set Fibre) = Z

/-- Linearity of the restriction to a specified subspace. -/
def linearRestrictionOn (f : Fibre → Scalar) (Z : Set Fibre) : Prop :=
  ∃ W : Submodule Scalar Fibre,
    (W : Set Fibre) = Z ∧
      ∃ L : W →ₗ[Scalar] Scalar,
        ∀ v : W, L v = f v.1

/-- A linear correction agrees with the negative of the shear on `Z`. -/
def correctsOn (ell : Fibre →ₗ[Scalar] Scalar)
    (f : Fibre → Scalar) (Z : Set Fibre) : Prop :=
  ∀ x : Fibre, x ∈ Z → ell x = -f x

/-- Claim 41602: every normalized fibre shear admits the stated affine repair,
with the original target regular copy retained and the repaired shear in the
exact two-closure of the generated pair. -/
def claim41602 : Prop :=
  ∀ f : Fibre → Scalar,
    f 0 = 0 →
      ∃ q : Permutation, ∃ ell : Fibre →ₗ[Scalar] Scalar,
        ∃ q' : Permutation,
          fibreShearFormula f q ∧
            let R := translationCopy
            let T := targetCopy q
            let Y := generatedPair R T
            isSubspace (shearZ f) ∧
              linearRestrictionOn f (shearZ f) ∧
                (∀ x : Fibre, x ∈ shearZ f →
                  ∀ v : Fibre, f (x + v) - f x = f v) ∧
                  correctsOn ell f (shearZ f) ∧
                    fibreShearFormula (fun v => f v + ell v) q' ∧
                      regularPermutationCopy T ∧
                        targetCopy q' = T ∧
                          q' ∈ twoClosure Y

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41602
