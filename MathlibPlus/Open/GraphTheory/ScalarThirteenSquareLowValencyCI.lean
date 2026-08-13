import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Open.GraphTheory

/-- Cell N4, scalar prime-square slice: ordinary undirected Cayley graphs on
`E(C₁₃²,3)` are CI through valency six and in the complementary range. -/
def scalarThirteenSquareLowAndComplementaryValencyCI : Prop :=
  let V := Multiplicative (Fin 2 → ZMod 13)
  let C := Multiplicative (ZMod 3)
  let IsScalarAction := fun (φ : C →* MulAut V) =>
    ∀ v : V,
      ((φ (Multiplicative.ofAdd (1 : ZMod 3))) v).toAdd =
        fun i => (3 : ZMod 13) * v.toAdd i
  (∃ φ : C →* MulAut V, IsScalarAction φ) ∧
  ∀ (φ : C →* MulAut V), IsScalarAction φ →
    let G := V ⋊[φ] C
    Fintype.card G = 507 ∧
    ∀ (S T : Set G),
      S = S⁻¹ → T = T⁻¹ →
      1 ∉ S → 1 ∉ T →
      (Set.ncard S ≤ 6 ∨ 500 ≤ Set.ncard S) →
      (Set.ncard T ≤ 6 ∨ 500 ≤ Set.ncard T) →
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
        ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
