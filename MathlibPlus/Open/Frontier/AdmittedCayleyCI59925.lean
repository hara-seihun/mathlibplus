import Mathlib

namespace MathlibPlus.Open.Frontier

abbrev F3Vector (r : ℕ) := Fin r → ZMod 3

def identityFree {r : ℕ} (S : Set (F3Vector r)) : Prop :=
  (0 : F3Vector r) ∉ S

def inverseClosed {r : ℕ} (S : Set (F3Vector r)) : Prop :=
  ∀ ⦃x : F3Vector r⦄, x ∈ S → -x ∈ S

def spansVectorSpace {r : ℕ} (U : Set (F3Vector r)) : Prop :=
  Submodule.span (ZMod 3) U = ⊤

def cayleyAdjacency {r : ℕ} (S : Set (F3Vector r))
    (x y : F3Vector r) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyGraphIso {r : ℕ} (S T : Set (F3Vector r)) : Prop :=
  ∃ e : F3Vector r ≃ F3Vector r,
    ∀ x y : F3Vector r,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

def ci_claim_59925 : Prop :=
  ∀ (r : ℕ),
    (r = 6 ∨ r = 7) →
    ∀ (S : Set (F3Vector r)),
      identityFree S →
      inverseClosed S →
      let U : Set (F3Vector r) := (Set.univ \ {0}) \ S
      spansVectorSpace U →
      Set.ncard U = 2 * r →
      ∀ (T : Set (F3Vector r)),
        identityFree T →
        inverseClosed T →
        cayleyGraphIso S T →
        (∃ A : F3Vector r ≃ₗ[ZMod 3] F3Vector r, A '' S = T) ∧
          ((r = 6 → Set.ncard S = 716) ∧
            (r = 7 → Set.ncard S = 2172))

end MathlibPlus.Open.Frontier
