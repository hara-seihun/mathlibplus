import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1003Claim28182
import MathlibPlus.Open.ResearchFormalization.R1003Claim28186

namespace MathlibPlus.Open.ResearchFormalization.R1003.Claim28189

abbrev HCoordinate := MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.HCoordinate
abbrev GCoordinate := MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.GCoordinate
abbrev OmegaH := MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.OmegaH
abbrev Omega := MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.Omega
abbrev EGroup := MathlibPlus.Open.GraphTheory.EC35Eight

open MathlibPlus.Open.ResearchFormalization.R1003.Claim28186

/-- The cubing map on the displayed coordinate carrier. -/
def coordinateAlpha (g : GCoordinate) : GCoordinate :=
  (g.1, (g.2.1, 3 * g.2.2))

/-- The normalized zero translation profile. -/
def zeroProfile : HCoordinate → ZMod 7 := fun _ => 0

/-- The exact normalized support-at-most-one profile domain. -/
def normalizedSupportAtMostOne (t : HCoordinate → ZMod 7) : Prop :=
  t hOne = 0 ∧
    (t = zeroProfile ∨ nonzeroNormalizedOneSupport t)

/-- The identity of the displayed semidirect-product coordinate group. -/
def coordinateOne : GCoordinate := (0, hOne)

/-- Regularity of the two actual transported right-regular copies. -/
def actualRegularPair (t : HCoordinate → ZMod 7) : Prop :=
  (∀ x y : Omega, ∃! p : Equiv.Perm Omega,
    p ∈ P ∧ p x = y) ∧
    (∀ x y : Omega, ∃! p : Equiv.Perm Omega,
      p ∈ Q t ∧ p x = y)

/-- Image of an ordered-pair relation under a point permutation. -/
def pairImage (τ : Equiv.Perm Omega) (R : Set (Omega × Omega)) :
    Set (Omega × Omega) :=
  Set.image (fun p : Omega × Omega => (τ p.1, τ p.2)) R

/-- The union of a displayed subfamily of paired orbitals. -/
def fusion (𝓕 : Set (Set (Omega × Omega))) : Set (Omega × Omega) :=
  ⋃ O : Set (Omega × Omega), ⋃ _ : O ∈ 𝓕, O

/-- The connection set read at the identity with one of the two labelings. -/
def labelingConnectionSet (lab : GCoordinate → Omega)
    (R : Set (Omega × Omega)) : Set GCoordinate :=
  {g | (lab coordinateOne, lab g) ∈ R}

/-- The actual subfamilies of the paired-orbital carrier. -/
def FusionSubfamily (t : HCoordinate → ZMod 7) :=
  {𝓕 : Set (Set (Omega × Omega)) //
    𝓕 ⊆ pairedOrbitals (generatedPair t)}

/-- The carrier of the actual unions of paired orbitals. -/
def ActualFusion (t : HCoordinate → ZMod 7) :=
  {R : Set (Omega × Omega) //
    ∃ 𝓕 : Set (Set (Omega × Omega)),
      𝓕 ⊆ pairedOrbitals (generatedPair t) ∧ R = fusion 𝓕}

/-- The exact power-of-two count of the actual fusions. -/
def fusionCount (t : HCoordinate → ZMod 7) (k : ℕ) : Prop :=
  Nat.card (ActualFusion t) = 2 ^ k

/-- CI transport of one actual fusion through the two actual regular labelings. -/
def fusionCITransported
    (t : HCoordinate → ZMod 7)
    (e : GCoordinate ≃ EGroup)
    (α : EGroup ≃* EGroup)
    (τ : Equiv.Perm Omega)
    (𝓕 : Set (Set (Omega × Omega))) : Prop :=
  let R := fusion 𝓕
  pairImage τ R = R ∧
    Set.image α
        (Set.image e (labelingConnectionSet lambda1 R)) =
      Set.image e (labelingConnectionSet (lambda2 t) R)

/-- Every actual fusion is transported with the one actual cubing transporter. -/
def everyActualFusionTransported
    (t : HCoordinate → ZMod 7)
    (e : GCoordinate ≃ EGroup)
    (α : EGroup ≃* EGroup)
    (τ : Equiv.Perm Omega) : Prop :=
  (∀ O : Set (Omega × Omega),
    O ∈ pairedOrbitals (generatedPair t) → pairImage τ O = O) ∧
    ∀ 𝓕 : Set (Set (Omega × Omega)),
      𝓕 ⊆ pairedOrbitals (generatedPair t) →
        fusionCITransported t e α τ 𝓕

/-- Claim 28189: every normalized support-at-most-one profile in the displayed
`E(C₃₅,8)` regular pair has all of its actual undirected paired-orbital fusions
ordinary-CI-equivalent through the two lifted labelings.  The orbital carriers,
profile domain, and cubing automorphism are all the displayed concrete ones. -/
def allSupportAtMostOnePairedOrbitalFusionsCIEquivalent : Prop :=
  ∃ e : GCoordinate ≃ EGroup,
    (∀ a b : GCoordinate,
      e (gMul a b) = e a * e b) ∧
      ∃ α : EGroup ≃* EGroup,
        (∀ g : GCoordinate,
          α (e g) = e (coordinateAlpha g)) ∧
          Nat.card {t : HCoordinate → ZMod 7 //
            normalizedSupportAtMostOne t} = 235 ∧
            ∀ t : HCoordinate → ZMod 7,
              normalizedSupportAtMostOne t →
                actualRegularPair t ∧
                  ((t = zeroProfile →
                      Set.ncard (pairedOrbitals (generatedPair t)) = 105 ∧
                        fusionCount t 105) ∧
                    (nonzeroNormalizedOneSupport t →
                      Set.ncard (pairedOrbitals (generatedPair t)) = 18 ∧
                        fusionCount t 18)) ∧
                  ∃ τ : Equiv.Perm Omega,
                    (∀ g : GCoordinate,
                      τ (lambda1 g) =
                        lambda2 t (coordinateAlpha g)) ∧
                      everyActualFusionTransported t e α τ

end MathlibPlus.Open.ResearchFormalization.R1003.Claim28189
