import Mathlib

namespace MathlibPlus.Open.CI

/--
The one-dimensional full-derivative affine-shadow claim, with the Cayley
connection sets and the two explicit shears included in the statement.
-/
def oneDimensionalFullDerivativeAffineShadow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    5 ≤ p →
      ∀ (B : Type*) [AddCommGroup B] [Module (ZMod p) B]
        [FiniteDimensional (ZMod p) B],
        ∀ (f : ZMod p → B),
          f 0 = 0 →
            let H : Submodule (ZMod p) B :=
              Submodule.span (ZMod p)
                (Set.range (fun y : ZMod p => f y - y • f 1))
            let S : Set (ZMod p × B) :=
              {z | ∃ (a : ZMod p) (h : B),
                a ≠ 0 ∧ h ∈ H ∧ z = (a, h - f a)}
            let T : Set (ZMod p × B) :=
              {z | ∃ (a : ZMod p) (h : B),
                a ≠ 0 ∧ h ∈ H ∧ z = (a, h)}
            let q : (ZMod p × B) → (ZMod p × B) :=
              fun z => (z.1, z.2 + f z.1)
            let L : (ZMod p × B) → (ZMod p × B) :=
              fun z => (z.1, z.2 + z.1 • f 1)
            let graphIso : Prop :=
              Function.Bijective q ∧
                ∀ (x y : ZMod p × B),
                  (x ≠ y ∧ y - x ∈ S) ↔
                    (q x ≠ q y ∧ q y - q x ∈ T)
            let linearAutoSends : Prop :=
              (∀ (c : ZMod p) (z : ZMod p × B),
                L (c • z) = c • L z) ∧
                (∀ (x y : ZMod p × B),
                  L (x + y) = L x + L y) ∧
                Function.Bijective L ∧ L '' S = T
            (∀ (a : ZMod p), a ≠ 0 →
              Submodule.span (ZMod p)
                (Set.range
                  (fun x : ZMod p => f (x + a) - f x - f a)) = H) ∧
              (∀ (z : ZMod p × B), z ∈ S → -z ∈ S) ∧
              (∀ (z : ZMod p × B), z ∈ T → -z ∈ T) ∧
              graphIso ∧
              linearAutoSends ∧
              (∀ (r : ℕ),
                r = 1 + Module.finrank (ZMod p) B →
                  ¬ (graphIso ∧ ¬ linearAutoSends))

end MathlibPlus.Open.CI
