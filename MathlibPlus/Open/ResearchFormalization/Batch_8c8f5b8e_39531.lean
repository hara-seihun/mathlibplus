import MathlibPlus.Open.ResearchFormalization.R1085.AllProperCIHarmless
import MathlibPlus.Open.ResearchFormalization.Lease01a0019fGroup
import MathlibPlus.Open.ResearchFormalization.AdmittedBatch_01a000eb525ca7c34f4fffd55f6717fb0

namespace MathlibPlus.Open.ResearchFormalization.ResearchFormalize39531

open MathlibPlus.Open.ResearchFormalization.Batch01
open MathlibPlus.Open.ResearchFormalization.R1085CI

private abbrev Base := MathlibPlus.Open.ResearchFormalization.R1085CI.Base
private abbrev Fiber := B3
private abbrev Carrier := Base × Fiber

private def nonzeroLine (L : AddSubgroup Fiber) : Prop :=
  (⊥ : AddSubgroup Fiber) < L ∧
    L < (⊤ : AddSubgroup Fiber) ∧
      Nat.card L = 3

private abbrev Line := {L : AddSubgroup Fiber // nonzeroLine L}

private abbrev LinePair :=
  {p : Line × Line // p.1.1 ≠ p.2.1}

private def literalProfile
    (p : LinePair) (q : Base → Equiv.Perm Fiber) : Prop :=
  q a0 = 1 ∧
    normalizedDisplacement (q a1) = p.1.1 ∧
    normalizedDisplacement (q a2) = p.1.2.1 ∧
    normalizedDisplacement (q a3) = p.1.2.1 ∧
    normalizedDisplacement (q a4) = p.1.1 ∧
    q a5 = 1 ∧
    q a6 = 1 ∧
    q a7 = 1

private def profileMap (q : Base → Equiv.Perm Fiber) : Carrier → Carrier :=
  fun x => (rho0 x.1, q x.1 x.2)

private def profilePresentation
    (q : Base → Equiv.Perm Fiber) (f : Equiv.Perm Carrier) : Prop :=
  f 0 = 0 ∧
    ∀ (a : Base) (b : Fiber),
      f (a, b) = profileMap q (a, b)

private def normalizedDerivative
    (f : Equiv.Perm Carrier) (s : Carrier) : Equiv.Perm Carrier :=
  Equiv.addRight (-(f s)) * f * Equiv.addRight s * f.symm

private def derivativeGroup (f : Equiv.Perm Carrier) :
    Subgroup (Equiv.Perm Carrier) :=
  Subgroup.closure (Set.range (normalizedDerivative f))

private def derivativeOrbit
    (f : Equiv.Perm Carrier) (x : Carrier) : Set Carrier :=
  {y | ∃ g : Equiv.Perm Carrier, g ∈ derivativeGroup f ∧ g x = y}

private def inverseCompatibleDerivativeBlock
    (f : Equiv.Perm Carrier) (C : Set Carrier) : Prop :=
  (∃ x : Carrier, C = derivativeOrbit f x) ∧
    ∀ y : Carrier, y ∈ C ↔ -y ∈ C

private def directedCayleyPresentation
    (S : Set Carrier) (f : Equiv.Perm Carrier) : Prop :=
  f 0 = 0 ∧
    ∀ x y : Carrier,
      y - x ∈ S ↔ f y - f x ∈ Set.image f S

private def additiveAutomorphismShadow
    (S T : Set Carrier) : Prop :=
  ∃ α : Carrier ≃+ Carrier, Set.image α S = T

private def directedCayleyHarmless (f : Equiv.Perm Carrier) : Prop :=
  ∀ S : Set Carrier,
    (0 : Carrier) ∉ S →
      (0 : Carrier) ∉ Set.image f S →
        directedCayleyPresentation S f →
          additiveAutomorphismShadow S (Set.image f S)

private def ordinaryCayleyHarmless (f : Equiv.Perm Carrier) : Prop :=
  ∀ S : Set Carrier,
    (0 : Carrier) ∉ S →
      (∀ x : Carrier, x ∈ S ↔ -x ∈ S) →
        (0 : Carrier) ∉ Set.image f S →
          (∀ x : Carrier, x ∈ Set.image f S ↔ -x ∈ Set.image f S) →
            directedCayleyPresentation S f →
              additiveAutomorphismShadow S (Set.image f S)

private def localActionOrbit
    (Γ : Subgroup (Equiv.Perm Fiber)) (x : Fiber) : Set Fiber :=
  {y | ∃ g : Equiv.Perm Fiber, g ∈ Γ ∧ g x = y}

private def localTransitive (Γ : Subgroup (Equiv.Perm Fiber)) : Prop :=
  ∀ x : Fiber, localActionOrbit Γ x = Set.univ

private def localTransitivityOrDegree72Closure
    (p : LinePair) (q : Base → Equiv.Perm Fiber) (f : Equiv.Perm Carrier) : Prop :=
  localTransitive
      (translatedCollisionAction Fiber (q a2) (q a3)
        p.1.1) ∨
    (Fintype.card Carrier = 72 ∧
      (∀ x : Carrier,
        Set.image f (derivativeOrbit f x) = derivativeOrbit f x) ∧
      (∀ C : Set Carrier,
        inverseCompatibleDerivativeBlock f C → Set.image f C = C))

private def profileHarmless
    (p : LinePair) (q : Base → Equiv.Perm Fiber) : Prop :=
  ∃ f : Equiv.Perm Carrier,
    profilePresentation q f ∧
      localTransitivityOrDegree72Closure p q f ∧
      (∀ x : Carrier,
        Set.image f (derivativeOrbit f x) = derivativeOrbit f x) ∧
      (∀ C : Set Carrier,
        inverseCompatibleDerivativeBlock f C → Set.image f C = C) ∧
      directedCayleyHarmless f ∧
      ordinaryCayleyHarmless f

/-- Claim 39531: the fixed rho-zero support-four chart has four nonzero
projective fibre lines, twelve ordered distinct-line profiles, 639 literal
choices on each of the four active rows, and every one of the resulting
literal maps is derivative-orbit-fixing and CI/DCI-harmless. -/
def claim39531_exact_literal_map_count : Prop :=
  Fintype.card Base = 8 ∧
    Nat.card Line = 4 ∧
    Nat.card LinePair = 12 ∧
    639 ^ 4 = 166726039041 ∧
    12 * 639 ^ 4 = 2000712468492 ∧
    (∀ p : LinePair,
      Nat.card {q : Base → Equiv.Perm Fiber // literalProfile p q} = 639 ^ 4 ∧
        ∀ q : Base → Equiv.Perm Fiber,
          literalProfile p q → profileHarmless p q) ∧
    Nat.card
        {x : LinePair × (Base → Equiv.Perm Fiber) //
          literalProfile x.1 x.2} = 12 * 639 ^ 4

end MathlibPlus.Open.ResearchFormalization.ResearchFormalize39531
