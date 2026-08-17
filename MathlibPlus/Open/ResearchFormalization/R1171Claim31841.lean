import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim31841

noncomputable section

private abbrev F5 := ZMod 5
private abbrev V := Fin 4 → F5

private def derivative (f : V → F5) (u v : V) : F5 :=
  f (v + u) - f v

private def translate (h : V → F5) (w v : V) : F5 :=
  h (v + w)

private def derivativeGenerators (f : V → F5) : Set (V → F5) :=
  {h | h = (fun _ : V => (1 : F5)) ∨
    ∃ u w : V, h = translate (derivative f u) w}

private def derivativeModule (f : V → F5) : Submodule F5 (V → F5) :=
  Submodule.span F5 (derivativeGenerators f)

private def lift (g : F5 → F5) : V → F5 :=
  fun v => g (v 0)

private def generatedImageAffine (f : V → F5) : Prop :=
  ∀ h : V → F5, h ∈ derivativeModule f →
    ∃ a : V →ᵃ[F5] F5, ∀ v : V, h v = a v

private def actualImageConjugate (f : V → F5) : Prop :=
  ∃ h : V → F5, h ∈ derivativeModule f ∧
    ∃ a : V →ᵃ[F5] F5, ∀ v : V, f v = h v + a v

private def quadraticLift : V → F5 :=
  fun v => (v 0) ^ 2

private def cubicLift : V → F5 :=
  fun v => (v 0) ^ 3

private def normalizedFunction (g : F5 → F5) : Prop :=
  g 0 = 0

private def affineRelabelingEquivalent
    (g h : F5 → F5) : Prop :=
  ∃ (a : F5 →ᵃ[F5] F5) (l : F5 ≃ᵃ[F5] F5) (u : F5),
    u ≠ 0 ∧ ∀ x : F5, h x = u * g (l x) + a x

private def fiveTuple
    (a₀ a₁ a₂ a₃ a₄ : F5) : F5 → F5 :=
  ![a₀, a₁, a₂, a₃, a₄]

private def classRepresentative : Fin 6 → F5 → F5 :=
  ![fiveTuple 0 0 0 0 0,
    fiveTuple 0 0 0 0 1,
    fiveTuple 0 0 0 1 1,
    fiveTuple 0 0 0 1 2,
    fiveTuple 0 0 0 1 4,
    fiveTuple 0 0 1 3 1]

private def normalizedClass (g : F5 → F5) : Set (F5 → F5) :=
  {h | normalizedFunction h ∧ affineRelabelingEquivalent g h}

private def classOrbitSize : Fin 6 → ℕ :=
  ![5, 100, 200, 200, 100, 20]

private def classModuleRank : Fin 6 → ℕ :=
  ![1, 4, 4, 4, 3, 2]

private def rankFourOneCoordinate : F5 → F5 :=
  ![0, 0, 0, 1, 2]

private def rankWitnesses : Prop :=
  Module.finrank F5 (derivativeModule (lift (fun x : F5 => x ^ 2))) = 2 ∧
    Module.finrank F5 (derivativeModule (lift (fun x : F5 => x ^ 3))) = 3 ∧
    Module.finrank F5 (derivativeModule (lift rankFourOneCoordinate)) = 4

private def sixAffineRelabelingClasses : Prop :=
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

/-- Claim 31841: the cubic lift refutes universal image-affineness, the
    quadratic lift refutes actual-image conjugacy, and the exact one-coordinate
    census has ranks two, three, and four across five nontrivial classes. -/
def threeRefutedQuotientImageHypotheses_claim31841 : Prop :=
  ¬ generatedImageAffine cubicLift ∧
    ¬ actualImageConjugate quadraticLift ∧
    rankWitnesses ∧
    sixAffineRelabelingClasses

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim31841
