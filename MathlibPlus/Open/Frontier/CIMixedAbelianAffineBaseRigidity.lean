import Mathlib

namespace MathlibPlus.Open

/--
The affine-base rigidity assertion for a fiber-system-preserving Cayley
isomorphism on `C₄ × F₃³`, with the explicitly stated automorphism
consequence.
-/
def mixedAbelianAffineBaseRigidity : Prop :=
  ∀ (S T : Set ((ZMod 4) × (Fin 3 → ZMod 3))),
    (∀ x, x ∈ S → -x ∈ S) →
    (∀ x, x ∈ T → -x ∈ T) →
    ∀ (A : (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)),
      ∀ (b : Fin 3 → ZMod 3),
        ∀ (σ : (Fin 3 → ZMod 3) → Equiv.Perm (ZMod 4)),
          let Φ : (ZMod 4) × (Fin 3 → ZMod 3) →
              (ZMod 4) × (Fin 3 → ZMod 3) :=
            fun x => (σ x.2 x.1, A x.2 + b)
          (∀ (x d : (ZMod 4) × (Fin 3 → ZMod 3)),
              d ∈ S ↔ Φ (x + d) - Φ x ∈ T) →
            ((T = {p : (ZMod 4) × (Fin 3 → ZMod 3) |
                ∃ (a : ZMod 4) (w : Fin 3 → ZMod 3),
                  p = (a, A w) ∧ (a, w) ∈ S} ∨
              T = {p : (ZMod 4) × (Fin 3 → ZMod 3) |
                ∃ (a : ZMod 4) (w : Fin 3 → ZMod 3),
                  p = (-a, A w) ∧ (a, w) ∈ S}) ∧
              ∃ e : ((ZMod 4) × (Fin 3 → ZMod 3)) ≃+
                  ((ZMod 4) × (Fin 3 → ZMod 3)),
                T = e '' S)

end MathlibPlus.Open
