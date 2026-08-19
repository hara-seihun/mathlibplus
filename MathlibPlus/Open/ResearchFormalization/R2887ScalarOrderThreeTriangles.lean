import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2887ScalarOrderThreeTriangles

noncomputable section

/-- Claim 47369: the exact scalar fixed-point-free order-three semidirect
Cayley graph has the right-Cayley coordinate triangles as its connected
components. -/
def scalarOrderThreeTriangleDecomposition_claim47369 : Prop :=
  ∀ (M : Type*) [Group M] [Finite M] [Nontrivial M],
    let C3 := Multiplicative (ZMod 3)
    let c : C3 := Multiplicative.ofAdd 1
    ∀ φ : C3 →* MulAut M,
      (∀ m : M, φ c m = m → m = 1) →
        let G := SemidirectProduct M C3 φ
        let cG : G := SemidirectProduct.inr c
        let S : Set G := {cG, cG ^ 2}
        ∀ Γ : SimpleGraph G,
          (∀ x y : G,
            Γ.Adj x y ↔ x ≠ y ∧ x⁻¹ * y ∈ S) →
            (∀ x : G, ∃! q : M × Fin 3,
              x = SemidirectProduct.mk q.1 (c ^ q.2.val)) ∧
            (∀ (m : M) (i : Fin 3) (y : G),
              Γ.Adj (SemidirectProduct.mk m (c ^ i.val)) y ↔
                y = SemidirectProduct.mk m (c ^ (i.val + 1)) ∨
                y = SemidirectProduct.mk m (c ^ (i.val + 2))) ∧
            (∀ m : M, ∀ i j : Fin 3, i ≠ j →
              Γ.Adj (SemidirectProduct.mk m (c ^ i.val))
                (SemidirectProduct.mk m (c ^ j.val))) ∧
            (∀ (m m' : M) (i j : Fin 3), m ≠ m' →
              ¬Γ.Adj (SemidirectProduct.mk m (c ^ i.val))
                (SemidirectProduct.mk m' (c ^ j.val)))

end

end MathlibPlus.Open.ResearchFormalization.R2887ScalarOrderThreeTriangles
