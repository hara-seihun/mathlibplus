import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 60170: subspace connection sets in the stated semidirect product are ordinary
undirected CI connection sets. -/
def subspaceSemidirectC3OrdinaryUndirectedCIClaim60170 : Prop :=
  ∀ (p : ℕ) [_hp : Fact (Nat.Prime p)],
    let F := ZMod p
    ∀ (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
      ∀ (omega : F),
        omega ^ 3 = 1 → omega ≠ 1 →
          let G := V × ZMod 3
          let gMul : G → G → G :=
            fun x y =>
              (x.1 + (omega ^ x.2.val) • y.1, x.2 + y.2)
          let gInv : G → G :=
            fun x =>
              (-(omega ^ (-x.2).val) • x.1, -x.2)
          let gOne : G := (0, 0)
          let S_U : Submodule F V → Set G :=
            fun U => {x | ∃ v : V, v ∈ U ∧ v ≠ 0 ∧ x = (v, 0)}
          ∀ (U : Submodule F V) (T : Set G),
            gOne ∉ T →
              (∀ x : G, x ∈ T → gInv x ∈ T) →
                (∃ e : G ≃ G,
                  ∀ x y : G,
                    (gMul (gInv x) y ∈ S_U U) ↔
                      (gMul (gInv (e x)) (e y) ∈ T)) →
                  ∃ α : G ≃ G,
                    (∀ x y : G,
                      α (gMul x y) = gMul (α x) (α y)) ∧
                      Set.image α (S_U U) = T

end MathlibPlus.Open.ResearchFormalizationBatch
