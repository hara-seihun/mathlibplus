import Mathlib

namespace MathlibPlus.Open.GraphTheory

open scoped BigOperators

noncomputable section

/-- Exact ordinary undirected Cayley CI property for a group. -/
def ordinaryUndirectedCI {G : Type*} [Group G] : Prop :=
  ∀ S T : Set G,
    1 ∉ S → 1 ∉ T →
    (∀ x : G, x ∈ S ↔ x⁻¹ ∈ S) →
    (∀ x : G, x ∈ T ↔ x⁻¹ ∈ T) →
    (∃ e : G ≃ G, ∀ x y : G,
      x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) →
    ∃ α : G ≃* G, α '' S = T

def scalarActionAtGenerator {n : ℕ} (ell : ZMod n)
    (action : Multiplicative (ZMod 3) →*
      MulAut (Multiplicative (ZMod n))) : Prop :=
  ∀ v : Multiplicative (ZMod n),
    action (.ofAdd 1) v = .ofAdd (ell * v.toAdd)

/-- Claim 43733: the fixed-point-free order-three scalar products in the
stated squarefree `N4` slice are ordinary undirected CI-groups. -/
def fixedPointFreeScalarOrderThreeCI : Prop :=
  ∀ (s : ℕ) (q : Fin s → ℕ),
    0 < s →
    (∀ i : Fin s,
      Nat.Prime (q i) ∧ 3 < q i ∧ q i % 3 = 1) →
    (∀ i j : Fin s, i ≠ j → q i ≠ q j) →
    (∀ (i : Fin s) (hi : i.1 + 1 < s),
      3 * Finset.prod (Finset.Iic i) q < q ⟨i.1 + 1, hi⟩) →
    let n := ∏ i : Fin s, q i
    Nat.Coprime n (Nat.totient n) →
    ∀ ell : ZMod n,
      IsUnit ell → ell ^ 3 = 1 → IsUnit (ell - 1) →
      ∀ action : Multiplicative (ZMod 3) →*
        MulAut (Multiplicative (ZMod n)),
        scalarActionAtGenerator ell action →
        let G := Multiplicative (ZMod n) ⋊[action]
          Multiplicative (ZMod 3)
        Nat.card G = 3 * n ∧ ordinaryUndirectedCI (G := G)

end

end MathlibPlus.Open.GraphTheory
