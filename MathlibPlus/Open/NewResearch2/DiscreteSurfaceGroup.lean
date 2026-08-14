import Mathlib

namespace MathlibPlus.Open.NewResearch2.DiscreteSurfaceGroup

/-- A construction that sees only the isomorphism class of an additive group. -/
def IsAddGroupInvariant {S : Type} (spectrum : Type → S) : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H],
    Nonempty (G ≃+ H) → spectrum G = spectrum H

/--
The discrete group `π₁(E(ℂ)) ≅ ℤ²` cannot carry enough information to
recover two distinct Frobenius polynomials.  The statement is phrased for
an arbitrary group-isomorphism-invariant output, so it does not replace the
proper spectrum by an unconstrained curve-dependent invariant.
-/
def claim12968 : Prop :=
  ∀ (S : Type) (spectrum : Type → S),
    IsAddGroupInvariant spectrum →
      ∀ (G₁ G₂ : Type) [AddCommGroup G₁] [AddCommGroup G₂],
        (e₁ : G₁ ≃+ (ℤ × ℤ)) →
        (e₂ : G₂ ≃+ (ℤ × ℤ)) →
        ∀ (P₁ P₂ : Polynomial ℤ), P₁ ≠ P₂ →
          ¬ ∃ recover : S → Polynomial ℤ,
              recover (spectrum G₁) = P₁ ∧ recover (spectrum G₂) = P₂

end MathlibPlus.Open.NewResearch2.DiscreteSurfaceGroup
