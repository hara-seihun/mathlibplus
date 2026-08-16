import Mathlib

namespace MathlibPlus.Open

/-- Claim 60176: the exact presented group carrier satisfies undirected CI in valency seven. -/
def coprimeShellProductsC7Q12ValencySevenCI : Prop :=
  let a : FreeGroup (Fin 2) := FreeGroup.of 0
  let b : FreeGroup (Fin 2) := FreeGroup.of 1
  let rels : Set (FreeGroup (Fin 2)) :=
    {a ^ 6, b ^ 2 * (a ^ 3)⁻¹, b⁻¹ * a * b * a}
  let Q12 := PresentedGroup rels
  let G := Multiplicative (ZMod 7) × Q12
  let adj : Set G → G → G → Prop :=
    fun U x y => ∃ s, s ∈ U ∧ y = x * s
  ∀ S T : Set G,
    Set.ncard S = 7 ∧
      Set.ncard T = 7 ∧
      1 ∉ S ∧
      1 ∉ T ∧
      (∀ g, g ∈ S → g⁻¹ ∈ S) ∧
      (∀ g, g ∈ T → g⁻¹ ∈ T) →
      (∃ e : G → G,
        Function.Bijective e ∧
          ∀ x y, adj S x y ↔ adj T (e x) (e y)) →
        ∃ α : G ≃* G, Set.image (fun g => α g) S = T

end MathlibPlus.Open
