import Mathlib

noncomputable section

namespace MathlibPlus.Open.GroupTheory.Claim31542

abbrev D10 := DihedralGroup 5
abbrev C2 := Multiplicative (ZMod 2)

private def derivedC5Subgroup31542 {A : Type*} [Group A] :
    Subgroup (A × D10) :=
  Subgroup.prod (⊥ : Subgroup A)
    (Subgroup.closure
      ({DihedralGroup.r (1 : ZMod 5)} : Set D10))

def automaticCharacterMatching_AxD10_claim31542 : Prop :=
  ∀ (A : Type*) [Fintype A] [Group A],
    Nat.Coprime (Fintype.card A) 10 →
      let G := A × D10
      let U := derivedC5Subgroup31542 (A := A)
      let H := A × C2
      let χ : H →* C2 := MonoidHom.snd A C2
      Nat.card U = 5 ∧
        (∀ W : Subgroup G, Nat.card W = 5 → W = U) ∧
        (∃ q : G →* H,
          Function.Surjective q ∧ q.ker = U) ∧
        χ.ker =
          Subgroup.prod (⊤ : Subgroup A) (⊥ : Subgroup C2) ∧
        (Subgroup.prod (⊤ : Subgroup A) (⊥ : Subgroup C2)).Characteristic ∧
        (∀ φ : H ≃* H, ∀ h : H, χ (φ h) = χ h)

end MathlibPlus.Open.GroupTheory.Claim31542

end
