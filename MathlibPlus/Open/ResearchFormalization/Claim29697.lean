import MathlibPlus.Algebra.TranslationShearClaim29695

namespace MathlibPlus.Open.ResearchFormalization.Claim29697

noncomputable section

/-- The defect subgroup at a fixed element of the finite group factor. -/
def defectSubgroup {A H : Type*} [AddCommGroup A] [Group H]
    (h : H) (τ : H → A) : AddSubgroup A :=
  AddSubgroup.closure (Set.range (fun k : H => τ (h * k) - τ k - τ h))

/-- Multiplication by a natural number on the additive quotient by `W`. -/
def quotientMultiplication {A : Type*} [AddCommGroup A]
    (W : AddSubgroup A) (m : ℕ) : A ⧸ W → A ⧸ W :=
  fun x => m • x

/-- Claim 29697: the quotient defect equation, its order iteration, the
order divisibility and quotient invertibility facts, and the resulting
membership of `τ h` in `W_h` are all retained. -/
def claim29697 : Prop :=
  ∀ {A H : Type*} [Fintype A] [AddCommGroup A] [Fintype H] [Group H]
    (h : H) (τ : H → A),
    τ 1 = 0 →
    Nat.gcd (Fintype.card A) (Fintype.card H) = 1 →
    let W := defectSubgroup h τ
    (∀ k : H,
      QuotientAddGroup.mk' W (τ (h * k)) =
        QuotientAddGroup.mk' W (τ k + τ h)) ∧
    let m := orderOf h
    m ∣ Fintype.card H ∧
      m • QuotientAddGroup.mk' W (τ h) = 0 ∧
      Function.Bijective (quotientMultiplication W m) ∧
      τ h ∈ W

end

end MathlibPlus.Open.ResearchFormalization.Claim29697
