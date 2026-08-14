import Mathlib

namespace MathlibPlus.Open.Research

def claim_55242 : Prop :=
  ∀ {ι C W Z : Type*}
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup Z]
    [Module ℚ C] [Module ℚ W] [Module ℚ Z]
    [FiniteDimensional ℚ C]
    [FiniteDimensional ℚ W]
    [FiniteDimensional ℚ Z]
    (L : C →ₗ[ℚ] W)
    (A : C →ₗ[ℚ] Z)
    (C_i : ι → Submodule ℚ C),
    (⨆ i, C_i i) = ⊤ →
    let K : Submodule ℚ C := L.ker
    let K_i : ι → Submodule ℚ C := fun i => C_i i ⊓ K
    let Kloc : Submodule ℚ C := ⨆ i, K_i i
    let Hloc : Submodule ℚ Z := Submodule.map A Kloc
    let H : Submodule ℚ Z := Submodule.map A K
    let hK : Kloc ≤ K := iSup_le fun _ => inf_le_right
    let hH : Hloc ≤ H := Submodule.map_mono hK
    let KlocK : Submodule ℚ K := Kloc.comap K.subtype
    let HlocH : Submodule ℚ H := Hloc.comap H.subtype
    let incl : Hloc →ₗ[ℚ] H :=
      Hloc.subtype.codRestrict H (fun x => hH x.property)
    ∃ (barA : (K ⧸ KlocK) →ₗ[ℚ] (Z ⧸ Hloc)),
      (∀ x : K, barA (KlocK.mkQ x) = Hloc.mkQ (A x)) ∧
      ∃ (response : H →ₗ[ℚ] LinearMap.range barA),
        (∀ x : H, (response x : Z ⧸ Hloc) = Hloc.mkQ x) ∧
        Function.Injective incl ∧
        Function.Surjective response ∧
        LinearMap.range incl = LinearMap.ker response ∧
        ∃ (equiv : (H ⧸ HlocH) ≃ₗ[ℚ] LinearMap.range barA),
          (∀ x : H, equiv (HlocH.mkQ x) = response x) ∧
          Module.finrank ℚ H =
            Module.finrank ℚ Hloc +
              Module.finrank ℚ (LinearMap.range barA) ∧
          ((∀ i, Submodule.map A (C_i i ⊓ K) = ⊥) →
            Hloc = ⊥ ∧ Function.Bijective response)

end MathlibPlus.Open.Research
