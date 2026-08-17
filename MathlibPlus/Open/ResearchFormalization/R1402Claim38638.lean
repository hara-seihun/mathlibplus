import MathlibPlus.Open.PrimeFiber

namespace MathlibPlus.Open.ResearchFormalization.R1402Claim38638

open MathlibPlus.Open.PrimeFiber

noncomputable section

/-- Claim 38638: on the exact prime-fiber orbit carrier, a base-component-
preserving affine repair has no condition on saturated components, but any
quiet component forces e=1 and forces the shift to be the potential
 difference. -/
def claim38638 : Prop :=
  ∀ (B : Type*) [Fintype B] (I : Type*) (p : ℕ), Nat.Prime p →
    ∀ (r : I → Equiv.Perm B) (β : I → B → ZMod p)
      (e : ZMod p) (ell : B → ZMod p) (qbar : Equiv.Perm B),
      e ≠ 0 →
        (fixesEveryPrimeFiberOrbit r β e ell qbar ↔
          (preservesEveryPrimeFiberComponent r qbar ∧
            ((∃ b₀ : B, closedVoltageSubgroup r β b₀ = ⊥) → e = 1) ∧
            (∀ (O : Set B) (b₀ : B) (W : AddSubgroup (ZMod p))
              (t : B → ZMod p),
              validPrimeFiberChoice r β O b₀ W t → W = ⊥ →
                ∀ b, b ∈ O →
                  ell b = t (qbar b) - t b)))

end

end MathlibPlus.Open.ResearchFormalization.R1402Claim38638
