import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2283

noncomputable section

abbrev W := Fin 2 → ZMod 7
abbrev GL2_7 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)
abbrev PGL2_7 := Matrix.ProjGenLinGroup (Fin 2) (ZMod 7)
abbrev D :=
  {L : Submodule (ZMod 7) W // Module.finrank (ZMod 7) L = 1}

def glLinearMap (M : GL2_7) : W →ₗ[ZMod 7] W :=
  Matrix.mulVecLin (M : Matrix (Fin 2) (Fin 2) (ZMod 7))

def glProjectiveAction (M : GL2_7) (L K : D) : Prop :=
  Submodule.map (glLinearMap M) L.1 = K.1

def pglProjectiveAction (g : PGL2_7) (L K : D) : Prop :=
  ∃ M : GL2_7,
    Matrix.ProjGenLinGroup.mk M = g ∧ glProjectiveAction M L K

def distinctTriple {α : Type*} (x y z : α) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z

def projectiveActionIsFunctional : Prop :=
  ∀ g : PGL2_7, ∀ L : D, ∃! K : D, pglProjectiveAction g L K

def projectiveActionIsFaithful : Prop :=
  ∀ g : PGL2_7,
    (∀ L : D, pglProjectiveAction g L L) → g = 1

def projectiveActionIsSharplyThreeTransitive : Prop :=
  ∀ L₁ L₂ L₃ K₁ K₂ K₃ : D,
    distinctTriple L₁ L₂ L₃ → distinctTriple K₁ K₂ K₃ →
      ∃! g : PGL2_7,
        pglProjectiveAction g L₁ K₁ ∧
        pglProjectiveAction g L₂ K₂ ∧
        pglProjectiveAction g L₃ K₃

/-- The one-dimensional subspaces, the linear group order, the faithful
projective quotient, and sharp ordered-triple transitivity. -/
def projectiveDirectionSharpThreeTransitivity_claim44388 : Prop :=
  Nat.card D = 8 ∧
    Nat.card GL2_7 = (7 ^ 2 - 1) * (7 ^ 2 - 7) ∧
    Nat.card GL2_7 = 2016 ∧
    Nat.card PGL2_7 = 336 ∧
    projectiveActionIsFunctional ∧
    projectiveActionIsFaithful ∧
    projectiveActionIsSharplyThreeTransitive

end

end MathlibPlus.Open.ResearchFormalization.R2283
