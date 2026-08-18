import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41604

noncomputable section

abbrev F5 := ZMod 5
abbrev V := Fin 4 → F5

def derivative (f : V → F5) (u v : V) : F5 :=
  f (v + u) - f v

def translate (h : V → F5) (w v : V) : F5 :=
  h (v + w)

def derivativeGenerators (f : V → F5) : Set (V → F5) :=
  {h | h = (fun _ : V => (1 : F5)) ∨
    ∃ u w : V, h = translate (derivative f u) w}

def derivativeModule (f : V → F5) : Submodule F5 (V → F5) :=
  Submodule.span F5 (derivativeGenerators f)

def lift (g : F5 → F5) : V → F5 :=
  fun v => g (v 0)

def actualImageConjugate (f : V → F5) : Prop :=
  ∃ h : V → F5, h ∈ derivativeModule f ∧
    ∃ a : V →ᵃ[F5] F5, ∀ v : V, f v = h v + a v

def normalizedFunction (g : F5 → F5) : Prop :=
  g 0 = 0

def affineRelabelingEquivalent (g h : F5 → F5) : Prop :=
  ∃ (a : F5 →ᵃ[F5] F5) (l : F5 ≃ᵃ[F5] F5) (u : F5),
    u ≠ 0 ∧ ∀ x : F5, h x = u * g (l x) + a x

def fiveTuple (a₀ a₁ a₂ a₃ a₄ : F5) : F5 → F5 :=
  ![a₀, a₁, a₂, a₃, a₄]

def classRepresentative : Fin 6 → F5 → F5 :=
  ![fiveTuple 0 0 0 0 0,
    fiveTuple 0 0 0 0 1,
    fiveTuple 0 0 0 1 1,
    fiveTuple 0 0 0 1 2,
    fiveTuple 0 0 0 1 4,
    fiveTuple 0 0 1 3 1]

def normalizedClass (g : F5 → F5) : Set (F5 → F5) :=
  {h | normalizedFunction h ∧ affineRelabelingEquivalent g h}

def classOrbitSize : Fin 6 → ℕ :=
  ![5, 100, 200, 200, 100, 20]

def classModuleRank : Fin 6 → ℕ :=
  ![1, 4, 4, 4, 3, 2]

def sixAffineRelabelingClasses : Prop :=
  (Set.ncard {g : F5 → F5 | normalizedFunction g} = 625) ∧
    (∀ g : F5 → F5, normalizedFunction g →
      ∃! i : Fin 6, affineRelabelingEquivalent (classRepresentative i) g) ∧
    (∀ i : Fin 6,
      Set.ncard (normalizedClass (classRepresentative i)) = classOrbitSize i) ∧
    (∀ i : Fin 6,
      Module.finrank F5
          (derivativeModule (lift (classRepresentative i))) =
        classModuleRank i) ∧
    (∀ i : Fin 6, i ≠ 0 →
      ¬ affineRelabelingEquivalent
          (classRepresentative i) (classRepresentative 0))

def fiveActualImageExceptions : Prop :=
  ∀ i : Fin 6, i ≠ 0 →
    ¬ actualImageConjugate (lift (classRepresentative i))

/-- Claim 41604: the exact normalized one-coordinate function carrier has
six affine-relabeling classes with the displayed representatives, orbit sizes,
and module ranks, and the five nonzero classes are actual-image exceptions. -/
def claim41604 : Prop :=
  sixAffineRelabelingClasses ∧ fiveActualImageExceptions

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41604
