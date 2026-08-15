import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

/-- Claim 52556: the translation radical and its quotient connection set. -/
def claim_52556 : Prop :=
  ∀ (p r : Nat), Nat.Prime p → p % 2 = 1 →
    let V := Fin r → ZMod p
    ∀ S : Finset V,
      S = S.image Neg.neg → 0 ∉ S →
      ∃ F : AddSubgroup V,
        (∀ u : V, u ∈ F ↔ S.image (fun s => s + u) = S) ∧
        (∀ s ∈ S, s ∉ F) ∧
        ∃ Sbar : Finset (V ⧸ F),
          (0 : V ⧸ F) ∉ Sbar ∧
          (∀ y ∈ Sbar, -y ∈ Sbar) ∧
          (∀ x : V, x ∈ S ↔ QuotientAddGroup.mk x ∈ Sbar) ∧
          (∀ T : Finset (V ⧸ F),
            (0 : V ⧸ F) ∉ T → (∀ y ∈ T, -y ∈ T) →
            (∀ x : V, x ∈ S ↔ QuotientAddGroup.mk x ∈ T) → T = Sbar)

/-- Claim 52639: a subdirect translation module over the ternary fibre. -/
def claim_52639 (e : Nat) {X : Type} [Fintype X]
    (M : AddSubgroup (X → (Fin e → ZMod 3))) : Prop :=
  ∀ (x : X) (d : Fin e → ZMod 3),
    ∃ m : X → (Fin e → ZMod 3), m ∈ M ∧ m x = d

private def fibreTranslate {D X : Type} [AddGroup D]
    (m : X → D) (z : D × X) : D × X :=
  (z.1 + m z.2, z.2)

/-- Claim 52640: every normalizer has affine block form. -/
def claim_52640 (e : Nat) {X : Type} [Fintype X]
    (M : AddSubgroup (X → (Fin e → ZMod 3)))
    (g : Equiv.Perm ((Fin e → ZMod 3) × X)) : Prop :=
  (∀ (x : X) (d : Fin e → ZMod 3),
    ∃ m : X → (Fin e → ZMod 3), m ∈ M ∧ m x = d) →
  ((∀ m : X → (Fin e → ZMod 3), m ∈ M →
      ∃ m' : X → (Fin e → ZMod 3), m' ∈ M ∧
        ∀ z, g (fibreTranslate m z) = fibreTranslate m' (g z)) ∧
    (∀ m' : X → (Fin e → ZMod 3), m' ∈ M →
      ∃ m : X → (Fin e → ZMod 3), m ∈ M ∧
        ∀ z, g (fibreTranslate m z) = fibreTranslate m' (g z))) →
  ∃ σ : Equiv.Perm X,
    (∃ α : X → ((Fin e → ZMod 3) ≃ₗ[ZMod 3] (Fin e → ZMod 3)),
      ∃ t : X → (Fin e → ZMod 3),
        ∀ (d : Fin e → ZMod 3) (x : X),
          g (d, x) = (α x d + t x, σ x))

end
end MathlibPlus.Open.FormalizationBatch
