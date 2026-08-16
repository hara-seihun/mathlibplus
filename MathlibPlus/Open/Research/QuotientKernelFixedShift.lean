import Mathlib

namespace MathlibPlus.Open

/-- Pullback along a surjective quotient identifies the quotient full shift with
its kernel-fixed subshift, with the right-shift convention made explicit. -/
def quotientKernelFixedShiftConjugacy
    (H Γ A : Type*)
    [Group H] [Group Γ] [Fintype A]
    [TopologicalSpace A] [DiscreteTopology A]
    (q : H →* Γ) : Prop :=
  Function.Surjective q →
  2 ≤ Fintype.card A →
  let X_N :=
    {x : H → A //
      ∀ n : q.ker, (fun h : H => x (h * (n : H))) = x}
  let Γ_surjunctive : Prop :=
    ∀ f : (Γ → A) → (Γ → A),
      Continuous f →
      Function.Injective f →
      (∀ g : Γ, ∀ x : Γ → A, ∀ k : Γ,
        f (fun z : Γ => x (z * g)) k = f x (k * g)) →
      Function.Surjective f
  let X_surjunctive : Prop :=
    ∀ f : X_N → X_N,
      Continuous f →
      Function.Injective f →
      (∀ h : H, ∀ x y : X_N,
        (∀ k : H, y.1 k = x.1 (k * h)) →
        ∀ k : H, (f y).1 k = (f x).1 (k * h)) →
      Function.Surjective f
  (∃ e : (Γ → A) ≃ₜ X_N,
      (∀ x : Γ → A, ∀ h : H, (e x).1 h = x (q h)) ∧
      (∀ h : H, ∀ x : Γ → A, ∀ k : H,
        (e (fun z : Γ => x (z * q h))).1 k = (e x).1 (k * h))) ∧
    (Γ_surjunctive ↔ X_surjunctive)

end MathlibPlus.Open
