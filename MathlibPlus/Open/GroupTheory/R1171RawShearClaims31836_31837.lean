import MathlibPlus.Open.GroupTheory.FiberShearClaim41596
import MathlibPlus.Open.ResearchFormalization.R1171Claim41590

namespace MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837

noncomputable section

abbrev FiberField := ZMod 5
abbrev FiberBase := Fin 4 → FiberField
abbrev FiberOmega := FiberField × FiberBase
abbrev FiberFunction := FiberBase → FiberField

/-- The fibrewise shear permutation, written through the dependent-sum fibre map. -/
def fiberShear (f : FiberFunction) : Equiv.Perm FiberOmega :=
  (Equiv.prodComm FiberField FiberBase).trans
    ((Equiv.sigmaEquivProd FiberBase FiberField).symm.trans
      ((Equiv.sigmaCongrRight
          (fun v : FiberBase => Equiv.addRight (f v))).trans
        ((Equiv.sigmaEquivProd FiberBase FiberField).trans
          (Equiv.prodComm FiberField FiberBase).symm)))

def fiberTranslations : Subgroup (Equiv.Perm FiberOmega) :=
  Subgroup.closure
    (Set.range (fun a : FiberOmega => Equiv.addRight a))

def fiberTarget (f : FiberFunction) : Subgroup (Equiv.Perm FiberOmega) :=
  fiberTranslations.map (MulAut.conj (fiberShear f)⁻¹)

def fiberDerivative (f : FiberFunction) (u : FiberBase) : FiberFunction :=
  fun v => f (v + u) - f v

def fiberTranslate (w : FiberBase) (m : FiberFunction) : FiberFunction :=
  fun v => m (v + w)

def fiberDerivativeGenerators (f : FiberFunction) : Set FiberFunction :=
  {h | h = (fun _ : FiberBase => (1 : FiberField)) ∨
    ∃ u w : FiberBase, h = fiberTranslate w (fiberDerivative f u)}

def fiberDerivativeModule (f : FiberFunction) :
    Submodule FiberField FiberFunction :=
  Submodule.span FiberField (fiberDerivativeGenerators f)

def fiberZ (f : FiberFunction) : Set FiberBase :=
  {v | ∀ m : fiberDerivativeModule f,
    (m : FiberFunction) v = (m : FiberFunction) 0}

def fiberGeneratedImage (f : FiberFunction) :
    Subgroup (Equiv.Perm FiberOmega) :=
  MathlibPlus.Open.ResearchFormalization.R1171Claim41590.generatedPair
    fiberTranslations (fiberTarget f)

def fiberTwoClosure (f : FiberFunction) : Set (Equiv.Perm FiberOmega) :=
  MathlibPlus.Open.ResearchFormalization.R1171Claim41590.twoClosure
    (fiberGeneratedImage f)

/-- Raw shear membership is equivalent to vanishing on the common level set of
all derivative-module functions. -/
def claim31836 : Prop :=
  ∀ (f : FiberFunction),
    f 0 = 0 →
      ((fiberShear f : Equiv.Perm FiberOmega) ∈ fiberTwoClosure f ↔
        ∀ v : FiberBase, v ∈ fiberZ f → f v = 0)

/-- Every normalized fibre shear admits the stated affine correction while its
conjugated regular target is unchanged. -/
def claim31837 : Prop :=
  ∀ (f : FiberFunction),
    f 0 = 0 →
      ∃ Z : Submodule FiberField FiberBase,
        (Z : Set FiberBase) = fiberZ f ∧
          (∀ x : FiberBase, x ∈ fiberZ f →
            ∀ v : FiberBase, f (x + v) - f x = f v) ∧
          ∃ ell : FiberBase →ₗ[FiberField] FiberField,
            (∀ x : FiberBase, x ∈ Z → ell x = -f x) ∧
              fiberTarget (fun v => f v + ell v) = fiberTarget f ∧
                ((fiberShear (fun v => f v + ell v) :
                    Equiv.Perm FiberOmega) ∈ fiberTwoClosure f)

end

end MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837
