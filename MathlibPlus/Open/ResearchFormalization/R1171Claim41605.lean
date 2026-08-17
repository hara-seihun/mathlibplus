import MathlibPlus.Open.GroupTheory.FiberShearClaim41596
import MathlibPlus.Open.ResearchFormalization.R1171Claim41590

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41605

noncomputable section

abbrev FiberField := ZMod 5
abbrev FiberBase := Fin 4 → FiberField
abbrev FiberOmega := FiberField × FiberBase

/-- The first derivative and its translates used by the generated image. -/
def derivative (f : FiberBase → FiberField) (u v : FiberBase) : FiberField :=
  f (v + u) - f v

def translate (h : FiberBase → FiberField) (w v : FiberBase) : FiberField :=
  h (v + w)

def derivativeModule (f : FiberBase → FiberField) :
    Submodule FiberField (FiberBase → FiberField) :=
  Submodule.span FiberField
    {h | h = (fun _ : FiberBase => (1 : FiberField)) ∨
      ∃ u w : FiberBase, h = translate (derivative f u) w}

/-- Affineness of the actual generated image, namely of every function in the
translation-derivative module, rather than affineness of the input shear. -/
def generatedImageAffine
    (M : Submodule FiberField (FiberBase → FiberField)) : Prop :=
  ∀ h : FiberBase → FiberField, h ∈ M →
    ∃ a : FiberBase →ᵃ[FiberField] FiberField,
      ∀ v : FiberBase, h v = a v

def zeroSpace
    (M : Submodule FiberField (FiberBase → FiberField)) : Set FiberBase :=
  {v | ∀ m : FiberBase → FiberField, m ∈ M → m v = m 0}

def zeroRepair
    (f : FiberBase → FiberField)
    (M : Submodule FiberField (FiberBase → FiberField))
    (ell : FiberBase →ₗ[FiberField] FiberField) : Prop :=
  ∀ v : FiberBase, v ∈ zeroSpace M → ell v = -f v

/-- The exact translation copy on `F₅ × F₅⁴`. -/
def translationGroup : Subgroup (Equiv.Perm FiberOmega) :=
  Subgroup.closure
    (Set.range (fun a : FiberOmega => Equiv.addRight a))

/-- The target copy obtained by conjugating the translations by a shear. -/
def targetGroup (q : Equiv.Perm FiberOmega) :
    Subgroup (Equiv.Perm FiberOmega) :=
  translationGroup.map (MulAut.conj q⁻¹)

def twoClosureConjugacy
    (R T Y : Subgroup (Equiv.Perm FiberOmega)) : Prop :=
  ∃ q : Equiv.Perm FiberOmega,
    q ∈ MathlibPlus.Open.ResearchFormalization.R1171Claim41590.twoClosure Y ∧
      MathlibPlus.Open.ResearchFormalization.R1171Claim41590.conjugateSubgroup
        q⁻¹ R = T

/-- Claim 41605: the exact quadratic and cubic one-coordinate examples,
including actual-image nonconjugacy and the linear zero repair with the same
regular target copy inside the generated two-closure. -/
def claim41605 : Prop :=
  ∀ [Fact (Nat.Prime 5)],
    let f2 : FiberBase → FiberField := fun v => (v 0) ^ 2
    let f3 : FiberBase → FiberField := fun v => (v 0) ^ 3
    (∃ q2 : Equiv.Perm FiberOmega,
      (∀ (z : FiberField) (v : FiberBase),
        q2 (z, v) = (z + f2 v, v)) ∧
      let R := translationGroup
      let T := targetGroup q2
      let Y := MathlibPlus.Open.ResearchFormalization.R1171Claim41590.generatedPair R T
      MathlibPlus.Open.ResearchFormalization.R1171Claim41590.regularPermutationCopy R ∧
        MathlibPlus.Open.ResearchFormalization.R1171Claim41590.regularPermutationCopy T ∧
        Module.finrank FiberField (derivativeModule f2) = 2 ∧
        Nat.card (↥Y) = 5 ^ 6 ∧
        Nat.card (↥(R ⊓ T)) = 5 ^ 4 ∧
        ¬ MathlibPlus.Open.ResearchFormalization.R1171Claim41590.conjugateInAmbient
            Y R T ∧
        ∃ ell : FiberBase →ₗ[FiberField] FiberField,
          zeroRepair f2 (derivativeModule f2) ell ∧
          ∃ qRepair : Equiv.Perm FiberOmega,
            (∀ (z : FiberField) (v : FiberBase),
              qRepair (z, v) = (z + (f2 v + ell v), v)) ∧
            qRepair ∈
              MathlibPlus.Open.ResearchFormalization.R1171Claim41590.twoClosure Y ∧
            MathlibPlus.Open.ResearchFormalization.R1171Claim41590.conjugateSubgroup
              qRepair⁻¹ R = T) ∧
    (∃ q3 : Equiv.Perm FiberOmega,
      (∀ (z : FiberField) (v : FiberBase),
        q3 (z, v) = (z + f3 v, v)) ∧
      let R := translationGroup
      let T := targetGroup q3
      let Y := MathlibPlus.Open.ResearchFormalization.R1171Claim41590.generatedPair R T
      MathlibPlus.Open.ResearchFormalization.R1171Claim41590.regularPermutationCopy R ∧
        MathlibPlus.Open.ResearchFormalization.R1171Claim41590.regularPermutationCopy T ∧
        Module.finrank FiberField (derivativeModule f3) = 3 ∧
        Nat.card (↥Y) = 5 ^ 7 ∧
        ¬ generatedImageAffine (derivativeModule f3))

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41605
