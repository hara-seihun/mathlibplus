import Mathlib

namespace MathlibPlus.Open.Research.R1661

def isAffine {V : Type} [AddGroup V] (g : Equiv.Perm V) : Prop :=
  ∃ b : V, ∃ L : V ≃+ V, ∀ x : V, g x = b + L x

def isRegular {V : Type} (T : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ x y : V, ∃! t : T, t.1 x = y

def isElementaryAbelian {V : Type} (p : ℕ)
    (T : Subgroup (Equiv.Perm V)) : Prop :=
  (∀ a b : T, a * b = b * a) ∧
    (∀ t : T, t.1 ^ p = 1)

def normalizesWithPower {V : Type} [AddGroup V]
    (p m : ℕ) (T : Subgroup (Equiv.Perm V)) (n : Equiv.Perm V) : Prop :=
  isAffine n ∧
    (∀ t : T, n * t.1 * n⁻¹ ∈ T) ∧
      (∀ t : T, n * t.1 * n⁻¹ = t.1 ^ m)

/-- An affine power normalizer can be translated to a linear normalizer without
changing its power action on the regular elementary-abelian subgroup. -/
def claim33030 : Prop :=
  ∀ (p r m : ℕ), Nat.Prime p → m % p ≠ 0 → m % p ≠ 1 →
    let V : Type := Fin r → ZMod p
    ∀ (T : Subgroup (Equiv.Perm V)) (n : Equiv.Perm V),
      (∀ t : T, isAffine t.1) →
        isRegular T →
          isElementaryAbelian p T →
            normalizesWithPower p m T n →
              ∃ u : T, ∃ L : V ≃+ V,
                (u.1 * n) 0 = 0 ∧
                  (∀ x : V, (u.1 * n) x = L x) ∧
                    (∀ t : T,
                      u.1 * n * (t.1) * (u.1 * n)⁻¹ = t.1 ^ m)

/-- Two affine scalar complements with the same nontrivial scalar part differ
by conjugation with a translation. -/
def claim33037 : Prop :=
  ∀ (p r : ℕ), Nat.Prime p → Odd p →
    ∀ scalar : ZMod p, scalar ≠ 0 → scalar ≠ 1 →
      ∀ b₁ b₂ : (Fin r → ZMod p),
        ∃ v : (Fin r → ZMod p),
          ∀ x : (Fin r → ZMod p),
            v + (scalar • (x - v) + b₁) = scalar • x + b₂

end MathlibPlus.Open.Research.R1661
