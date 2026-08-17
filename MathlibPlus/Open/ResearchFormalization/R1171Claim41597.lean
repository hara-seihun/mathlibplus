import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41597

noncomputable section

abbrev F5 := ZMod 5
abbrev V := Fin 4 → F5
abbrev Ω := F5 × V

/-- The fibre shear and its explicit inverse formula. -/
def fibreShear (f : V → F5) : Ω → Ω :=
  fun z => (z.1 + f z.2, z.2)

def fibreShearInverse (f : V → F5) : Ω → Ω :=
  fun z => (z.1 - f z.2, z.2)

/-- The natural translation copy on the exact F₅ × F₅⁴ carrier. -/
def translationPermutation (a : Ω) : Equiv.Perm Ω :=
  Equiv.addLeft a

def regularCopy : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure (Set.range translationPermutation)

def conjugationHom {G : Type*} [Group G] (g : G) : G →* G :=
  (MulAut.conj g : G ≃* G).toMonoidHom

def conjugateSubgroup {G : Type*} [Group G]
    (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (conjugationHom g)

/-- T = q_f⁻¹ R q_f and Y_f = ⟨R,T⟩ for a supplied exact shear
 permutation q. -/
def targetCopy (q : Equiv.Perm Ω) : Subgroup (Equiv.Perm Ω) :=
  conjugateSubgroup q.symm regularCopy

def generatedImage (q : Equiv.Perm Ω) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure
    ((regularCopy : Set (Equiv.Perm Ω)) ∪
      (targetCopy q : Set (Equiv.Perm Ω)))

/-- Translation and first difference on the function module F₅^V. -/
def translateFunction (w : V) (h : V → F5) : V → F5 :=
  fun x => h (x + w)

def firstDifference (u : V) (f : V → F5) : V → F5 :=
  fun x => f (x + u) - f x

def constantOne : V → F5 := fun _ => 1

def derivativeGenerators (f : V → F5) : Set (V → F5) :=
  {constantOne} ∪
    {h | ∃ u w : V, h = translateFunction w (firstDifference u f)}

/-- M_f is the F₅-span of one and all translated first differences. -/
def derivativeModule (f : V → F5) : Submodule F5 (V → F5) :=
  Submodule.span F5 (derivativeGenerators f)

/-- The translation action used in the semidirect product description. -/
def translatedModuleFunction (w : V) (m : derivativeModule f) : V → F5 :=
  translateFunction w (m : V → F5)

/-- Coordinates for a semidirect-product identification.  The displayed
 multiplication law is the law induced by the concrete fibre maps
 `(z,v) ↦ (z + m v, v + w)`. -/
def semidirectCoordinates
    (f : V → F5) (q : Equiv.Perm Ω)
    (e : (generatedImage q : Type) ≃ (derivativeModule f × V)) : Prop :=
  (∀ x : generatedImage q, ∀ y : generatedImage q,
    ((e (x * y)).1 : V → F5) =
      (e y).1 + translatedModuleFunction (e y).2 (e x).1 ∧
    (e (x * y)).2 = (e x).2 + (e y).2) ∧
    (∀ x : generatedImage q, ∀ z : Ω,
      (x : Equiv.Perm Ω) z =
        (z.1 + ((e x).1 : V → F5) z.2, z.2 + (e x).2))

/-- Claim 41597: the actual generated image of the two concrete regular
 copies is the derivative module semidirect the translation group, with the
 exact order formula. -/
def claim41597 : Prop :=
  ∀ f : V → F5, f 0 = 0 →
    ∃ q : Equiv.Perm Ω,
      (∀ z : Ω, q z = fibreShear f z) ∧
        (∀ z : Ω, q.symm z = fibreShearInverse f z) ∧
          ∃ e : (generatedImage q : Type) ≃ (derivativeModule f × V),
            semidirectCoordinates f q e ∧
              Nat.card (generatedImage q) =
                5 ^ (4 + Module.finrank F5 (derivativeModule f))

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41597
