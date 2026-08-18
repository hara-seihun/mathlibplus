import MathlibPlus.Open.ResearchFormalization.R0341.Claim20128

namespace MathlibPlus.Open.ResearchFormalization.R0341Claim20121_20127

open MathlibPlus.Open.ResearchFormalization.R0341.Claim20128

noncomputable section

/-- The zero-based presentation of the admitted k-block diagonal stack: the
parameter q gives k=q+1 blocks, with q independent diagonal variables. -/
def claim20121 : Prop :=
  ∀ (F R E : Type*) [Field F] [Infinite F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (q : ℕ),
    Function.Injective
        (fun je : Fin q × E =>
          (MvPolynomial.X je : PolynomialRing F q E)) ∧
      (∀ (r : R) (e : E),
        genericDiagonalStack L q (0, r) e =
          algebraMap F (GenericField F q E) (L r e)) ∧
      (∀ (j : Fin q) (r : R) (e : E),
        genericDiagonalStack L q (j.succ, r) e =
          algebraMap F (GenericField F q E) (L r e) *
            algebraMap (PolynomialRing F q E) (GenericField F q E)
              (MvPolynomial.X (j, e)))

/-- For q+1 stacked blocks, the generic stack is injective exactly when every
column subset satisfies the k-fold rank capacity inequality. -/
def claim20127 : Prop :=
  ∀ (F R E : Type*) [Field F] [Infinite F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (q : ℕ),
    genericStackInjective L q ↔
      ∀ X : Finset E,
        X.card ≤ (q + 1) * columnRank L X

end

end MathlibPlus.Open.ResearchFormalization.R0341Claim20121_20127
