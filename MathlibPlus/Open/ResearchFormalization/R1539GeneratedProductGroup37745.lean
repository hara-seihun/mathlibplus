import Mathlib.GroupTheory.SpecificGroups.Alternating

open Classical

namespace MathlibPlus.Open.ResearchFormalization.R1539GeneratedProductGroup37745

noncomputable section

abbrev A4 := alternatingGroup (Fin 4)
abbrev Omega := ZMod 5 × A4
abbrev ProductGroup := ZMod 5 × A4 × A4

/-- The three exact action factors on `C₅ × A₄`. -/
def cTranslation (c : ZMod 5) : Equiv.Perm Omega :=
  Equiv.prodCongr (Equiv.addRight c) (Equiv.refl A4)

def leftA4Action (a : A4) : Equiv.Perm Omega :=
  Equiv.prodCongr (Equiv.refl (ZMod 5)) (Equiv.mulLeft a)

def rightA4Action (a : A4) : Equiv.Perm Omega :=
  Equiv.prodCongr (Equiv.refl (ZMod 5)) (Equiv.mulRight a)

def cFactor : Set (Equiv.Perm Omega) :=
  Set.range cTranslation

def leftFactor : Set (Equiv.Perm Omega) :=
  Set.range (fun a : A4 => leftA4Action a)

def rightFactor : Set (Equiv.Perm Omega) :=
  Set.range (fun a : A4 => rightA4Action a)

def H : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure (cFactor ∪ leftFactor)

def K : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure (cFactor ∪ rightFactor)

def generatedX : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure ((H : Set (Equiv.Perm Omega)) ∪
    (K : Set (Equiv.Perm Omega)))

/-- Claim 37745: the exact left/right regular pair generates the direct
product of the `C₅`, left `A₄`, and right `A₄` factors, with order 720 and
transitive action. -/
def claim37745 : Prop :=
  Nonempty (H ≃* (ZMod 5 × A4)) ∧
    Nonempty (K ≃* (ZMod 5 × A4)) ∧
      Nonempty (generatedX ≃* ProductGroup) ∧
        Nat.card generatedX = 720 ∧
          ∀ x y : Omega, ∃ g : generatedX, g.1 x = y

end

end MathlibPlus.Open.ResearchFormalization.R1539GeneratedProductGroup37745
