import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2668Claim42293

noncomputable section

abbrev ReducedGround := Fin 4
abbrev ReducedSet := Finset ReducedGround
abbrev ReducedFamily := Finset ReducedSet

/-- Frequency of a reduced coordinate in a reduced layer. -/
def layerFrequency (F : ReducedFamily) (w : ReducedGround) : ℕ :=
  (F.filter (fun A => w ∈ A)).card

/-- The two-bit category determined by membership in the two roots. -/
def rootCategory (R₁ R₂ : ReducedSet) (w : ReducedGround) : Fin 2 × Fin 2 :=
  (if w ∈ R₁ then (1 : Fin 2) else 0,
    if w ∈ R₂ then (1 : Fin 2) else 0)

/-- Claim 42293: exact singleton traces and the common-root witnesses. -/
def claim42293 : Prop :=
  let L : ReducedFamily :=
    {∅, {0, 1, 2}, {0, 1, 2, 3}}
  let U : ReducedFamily :=
    {{0, 1, 3}, {0, 1, 2, 3}}
  let R₁ : ReducedSet := {0, 2, 3}
  let R₂ : ReducedSet := {1, 2, 3}
  let p₁p₂ : ReducedSet := {0, 1}
  let p₁ : ReducedSet := {0}
  let p₂ : ReducedSet := {1}
  let x : ReducedGround := 2
  let z : ReducedGround := 3
  R₁ ∩ p₁p₂ = p₁ ∧
    R₂ ∩ p₁p₂ = p₂ ∧
    rootCategory R₁ R₂ x = ((1 : Fin 2), (1 : Fin 2)) ∧
    rootCategory R₁ R₂ z = ((1 : Fin 2), (1 : Fin 2)) ∧
    (layerFrequency L x, layerFrequency U x) = (2, 1) ∧
    (layerFrequency L z, layerFrequency U z) = (1, 2)

end

end MathlibPlus.Open.ResearchFormalization.R2668Claim42293
