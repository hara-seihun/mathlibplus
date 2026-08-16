import Mathlib

namespace MathlibPlus.Open

noncomputable def claim_60638 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    5 ≤ p →
      ∀ (X : Type*) [AddCommGroup X] [Module (ZMod p) X]
        [FiniteDimensional (ZMod p) X] (u : X),
        let U : Submodule (ZMod p) X :=
          Submodule.span (ZMod p) ({u} : Set X)
        Nat.card U = p →
          let D : Type := (ZMod p) × (ZMod p)
          let a : D := (1, 0)
          let b : D := (0, 1)
          ∀ (h : X), h ∈ U → h ≠ 0 →
            let W : Set (X → ZMod p) :=
              {w | ∀ (x : X), ∑ r : ZMod p, w (x + r • u) = 0}
            let k_w : (X → ZMod p) → X → D :=
              fun w x => w x • a + w (x - h) • b
            let M_h : Set (X → D) := Set.image k_w W
            ∀ (x y : X), x ≠ y →
              Set.image (fun w => k_w w y - k_w w x) W =
                (Set.univ : Set D)

end MathlibPlus.Open
