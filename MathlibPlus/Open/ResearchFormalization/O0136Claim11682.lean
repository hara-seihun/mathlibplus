import MathlibPlus.Open.Analysis.BatchO0136.Claim11681

namespace MathlibPlus.Open.ResearchFormalization.O0136Claim11682

noncomputable section

/-- Claim 11682: the cocycle inverse is typed at the transported fibre, and an
involution yields a square only after the fibre is fixed (or identified). -/
def claim11682_typedCocycleInverse : Prop :=
  ∀ (K W O M : Type*)
    [Field K] [Group W] [MulAction W O]
    [AddCommGroup M] [Module K M]
    (V : O → Type*)
    [∀ o : O, AddCommGroup (V o)]
    [∀ o : O, Module K (V o)]
    (N : ∀ (w : W) (x : O), V x ≃ₗ[K] V (w • x)),
    (∀ (g h : W) (x : O),
      HEq (N (g * h) x)
        ((N h x).trans (N g (h • x)))) →
      (∀ (w : W) (x : O),
        HEq
          ((N w x).trans (N w⁻¹ (w • x)))
          (LinearEquiv.refl K (V x))) ∧
        (∀ (s : W) (x : O),
          s * s = 1 →
            HEq
              ((N s x).trans (N s (s • x)))
              (LinearEquiv.refl K (V x)) ∧
              (s • x = x → HEq (N s (s • x)) (N s x)))

end

end MathlibPlus.Open.ResearchFormalization.O0136Claim11682
