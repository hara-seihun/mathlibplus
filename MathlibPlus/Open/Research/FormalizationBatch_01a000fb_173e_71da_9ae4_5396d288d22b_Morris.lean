import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_173e_71da_9ae4_5396d288d22b

noncomputable section
local instance instDecidableEqMorris (α : Type*) : DecidableEq α := Classical.decEq α

abbrev morrisW := Fin 3 → ZMod 3
abbrev morrisV := Fin 5 → ZMod 3
abbrev morrisAmbient := morrisW × morrisV

def morrisCorrection (w : morrisW) : morrisV := fun i =>
  if i = 0 then w 0 * (w 1)^2
  else if i = 1 then w 0 * (w 2)^2
  else if i = 2 then (w 1)^2 * w 2
  else if i = 3 then w 1 * (w 2)^2
  else w 0 * w 1 * w 2

def morrisShear (x : morrisAmbient) : morrisAmbient :=
  (x.1, x.2 + morrisCorrection x.1)

def morrisVerticalSubmodule : Submodule (ZMod 3) morrisAmbient :=
  (LinearMap.fst (ZMod 3) morrisW morrisV).ker

def morrisVerticalKernel (U : Submodule (ZMod 3) morrisAmbient) :
    Submodule (ZMod 3) morrisV :=
  Submodule.comap (LinearMap.inr (ZMod 3) morrisW morrisV) U

def morrisFullProjection (U : Submodule (ZMod 3) morrisAmbient) : Prop :=
  Function.Surjective (fun u : U => (u.1).1)

def morrisImageSet (U : Submodule (ZMod 3) morrisAmbient) :
    Set morrisAmbient := morrisShear '' (U : Set morrisAmbient)

def morrisImageIsLinear (U : Submodule (ZMod 3) morrisAmbient) : Prop :=
  ∃ K : Submodule (ZMod 3) morrisAmbient, (K : Set morrisAmbient) = morrisImageSet U

def morrisCorrectionModulo
    (K : Submodule (ZMod 3) morrisV) (w : morrisW) : morrisV ⧸ K :=
  Submodule.Quotient.mk (morrisCorrection w)

def morrisCorrectionAdditiveModulo
    (K : Submodule (ZMod 3) morrisV) : Prop :=
  ∀ x y : morrisW,
    morrisCorrectionModulo K (x + y) =
      morrisCorrectionModulo K x + morrisCorrectionModulo K y

def morrisStandardVector (i : Fin 3) : morrisW := fun j => if j = i then 1 else 0

/-- The full-projection obstruction for the specified Morris correction. -/
def claim52788 : Prop :=
  ∀ U : Submodule (ZMod 3) morrisAmbient,
    morrisFullProjection U →
    (Module.finrank (ZMod 3) (morrisVerticalKernel U) = 3 ∨
      Module.finrank (ZMod 3) (morrisVerticalKernel U) = 4) →
    ¬ morrisImageIsLinear U

/-- Graph modulo kernel, additivity modulo the kernel, and the spanning residue. -/
def claim52789 : Prop :=
  (∀ U : Submodule (ZMod 3) morrisAmbient, morrisFullProjection U →
    ∃ ell : morrisW →ₗ[ZMod 3]
        (morrisV ⧸ morrisVerticalKernel U),
      ∀ w : morrisW, ∀ v : morrisV,
        (w, v) ∈ U ↔
          ell w = Submodule.Quotient.mk v) ∧
  (∀ U : Submodule (ZMod 3) morrisAmbient,
    morrisFullProjection U → morrisImageIsLinear U →
    morrisCorrectionAdditiveModulo (morrisVerticalKernel U)) ∧
  (∀ i : Fin 3, morrisCorrection (morrisStandardVector i) = 0) ∧
  (∀ K : Submodule (ZMod 3) morrisV,
    morrisCorrectionAdditiveModulo K →
    ∀ w, morrisCorrection w ∈ K) ∧
  Set.ncard (Set.range morrisCorrection) = 17 ∧
  Submodule.span (ZMod 3) (Set.range morrisCorrection) = ⊤ ∧
  Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range morrisCorrection)) = 5

/-- The exact finite Grassmannian and rank-five exclusion certificate. -/
def claim52790 : Prop :=
  Set.ncard {K : Submodule (ZMod 3) morrisV |
      Module.finrank (ZMod 3) K = 3} = 1210 ∧
  (∀ K : Submodule (ZMod 3) morrisV,
    Module.finrank (ZMod 3) K = 3 →
    ¬ (Set.range morrisCorrection ⊆ (K : Set morrisV))) ∧
  (∀ K : Submodule (ZMod 3) morrisV,
    Module.finrank (ZMod 3) K = 4 →
    ¬ (Set.range morrisCorrection ⊆ (K : Set morrisV)))

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_173e_71da_9ae4_5396d288d22b
