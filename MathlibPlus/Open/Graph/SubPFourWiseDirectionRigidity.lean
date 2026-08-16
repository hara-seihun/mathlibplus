import Mathlib

namespace MathlibPlus.Open.Graph

def subPFourWiseDirectionRigidity : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : Fact p.Prime := ⟨hp⟩
    5 ≤ p →
      ∀ (V W : Type*) [AddCommGroup V] [AddCommGroup W]
        [Module (ZMod p) V] [Module (ZMod p) W]
        [FiniteDimensional (ZMod p) V] [FiniteDimensional (ZMod p) W],
        Module.finrank (ZMod p) V = Module.finrank (ZMod p) W →
          ∀ (m : ℕ) (s : Fin m → V) (S : Set V),
            S = {x | ∃ i : Fin m, x = s i ∨ x = -s i} →
              0 ∉ S →
                (∀ x ∈ S, -x ∈ S) →
                  (∀ i j : Fin m, i ≠ j → s i ≠ s j) →
                    (∀ i j : Fin m, s i ≠ -s j) →
                      Submodule.span (ZMod p) (Set.range s) = ⊤ →
                        m < p →
                          (∀ I : Finset (Fin m), I.card ≤ 4 →
                            LinearIndependent (ZMod p) (fun i : I => s i.1)) →
                            ∀ (T : Set W),
                              0 ∉ T →
                                (∀ x ∈ T, -x ∈ T) →
                                  ∀ (q : V ≃ W),
                                    (∀ x y : V,
                                      y - x ∈ S ↔ q y - q x ∈ T) →
                                      ∃ L : V ≃ₗ[ZMod p] W,
                                        (∀ x : V, q x = q 0 + L x) ∧
                                          Set.image L S = T

end MathlibPlus.Open.Graph
