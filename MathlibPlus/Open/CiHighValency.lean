import Mathlib

namespace MathlibPlus.Open.CiHighValency

abbrev V (r : ℕ) := Fin r → ZMod 3

def punctured (r : ℕ) : Set (V r) := Set.univ \ {0}

def inverseClosed {r : ℕ} (S : Set (V r)) : Prop :=
  ∀ ⦃x : V r⦄, x ∈ S → -x ∈ S

def cayleyAdj {r : ℕ} (S : Set (V r)) (x y : V r) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyGraphIso {r : ℕ} (S T : Set (V r)) (e : V r ≃ V r) : Prop :=
  ∀ x y : V r, cayleyAdj S x y ↔ cayleyAdj T (e x) (e y)

def highValencyClass (r : ℕ) (S : Set (V r)) : Prop :=
  (r = 6 → Set.ncard S ∈ ({714, 712} : Set ℕ)) ∧
    (r = 7 → Set.ncard S ∈ ({2170, 2168} : Set ℕ))

def claim59997 : Prop :=
  ∀ (r : ℕ),
    r ∈ ({6, 7} : Set ℕ) →
      ∀ (S : Set (V r)),
        S ⊆ punctured r →
          inverseClosed S →
            let U := punctured r \ S
            Submodule.span (ZMod 3) U = ⊤ →
              Set.ncard U ∈ ({2 * r + 2, 2 * r + 4} : Set ℕ) →
                highValencyClass r S ∧
                  ∀ (T : Set (V r)),
                    T ⊆ punctured r →
                      inverseClosed T →
                        ∀ (e : V r ≃ V r),
                          cayleyGraphIso S T e →
                            ∃ A : V r ≃ₗ[ZMod 3] V r, A '' S = T

end MathlibPlus.Open.CiHighValency
