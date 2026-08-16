import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch60250_60251_60252_60253

def q12GeneratorA60250 : FreeGroup (Fin 2) := FreeGroup.of 0

def q12GeneratorB60250 : FreeGroup (Fin 2) := FreeGroup.of 1

def q12Relations60250 : Set (FreeGroup (Fin 2)) :=
  {q12GeneratorA60250 ^ 6,
    q12GeneratorB60250 ^ 2 * q12GeneratorA60250 ^ (-3 : ℤ),
    q12GeneratorB60250⁻¹ * q12GeneratorA60250 * q12GeneratorB60250 *
      q12GeneratorA60250}

abbrev quaternionGroup12_60250 : Type := PresentedGroup q12Relations60250
abbrev cyclicGroup7_60250 : Type := Multiplicative (ZMod 7)

def cayleyGraph60250 (S : Set (cyclicGroup7_60250 × quaternionGroup12_60250)) :
    SimpleGraph (cyclicGroup7_60250 × quaternionGroup12_60250) :=
  SimpleGraph.fromRel (fun x y => x⁻¹ * y ∈ S)

def identityFreeInverseClosed60250 [Group G] (S : Set G) : Prop :=
  S ⊆ {x | x ≠ 1} ∧ ∀ x, x ∈ S → x⁻¹ ∈ S

def Claim60250 : Prop :=
  let G := cyclicGroup7_60250 × quaternionGroup12_60250
  ∀ S T : Set G,
    identityFreeInverseClosed60250 S ∧ identityFreeInverseClosed60250 T ∧
      ((S.ncard = 11 ∧ T.ncard = 11) ∨
        (S.ncard = 72 ∧ T.ncard = 72)) →
    (cayleyGraph60250 S ≃g cayleyGraph60250 T) →
    ∃ α : MulAut G, α '' S = T

end MathlibPlus.Open.ResearchFormalization.Batch60250_60251_60252_60253
