import Mathlib

noncomputable section
open Set

namespace MathlibPlus.Open.FormalizationBatch.R4643S3

abbrev F₅ := ZMod 5
abbrev Ambient := Fin 6 → F₅

private def basis (i : Fin 6) : Ambient := fun j => if j = i then 1 else 0

private def e₁ : Ambient := basis 0
private def e₂ : Ambient := basis 1
private def e₃ : Ambient := basis 2

private def movedFlat : Set Ambient :=
  {p | ∃ a b : F₅, p = a • e₁ + b • e₂}

private def transposition : Ambient → Ambient := fun p =>
  if p = 0 then e₃ else if p = e₃ then 0 else p

private def affineTwoFlat (p d₁ d₂ : Ambient) : Set Ambient :=
  {q | ∃ a b : F₅, q = p + a • d₁ + b • d₂}

private def isAffineTwoFlat (S : Set Ambient) : Prop :=
  ∃ p d₁ d₂ : Ambient,
    LinearIndependent F₅ ![d₁, d₂] ∧ S = affineTwoFlat p d₁ d₂

private def completeGraphAutomorphism (π : Ambient → Ambient) : Prop :=
  Function.Bijective π ∧ ∀ p q : Ambient, p ≠ q ↔ π p ≠ π q

/-- Claim 52456: the moved affine block and non-affine automorphism witness. -/
def claim52456 : Prop :=
  let E : Set Ambient := movedFlat
  let π : Ambient → Ambient := transposition
  completeGraphAutomorphism π ∧
    π '' E = (E \ {0}) ∪ {e₃} ∧
    ¬ isAffineTwoFlat (π '' E) ∧
    e₁ + e₃ ∉ π '' E ∧
    (π 0 - 0) ≠ (π e₁ - e₁)

end MathlibPlus.Open.FormalizationBatch.R4643S3
