import MathlibPlus.Open.Research.QuaternionBatch

namespace MathlibPlus.Open.Research.R1060MarkedShadow32948

open MathlibPlus.Open.Research.QuaternionBatch

noncomputable section

private def inverseLayer (i : Fin 4) : Fin 4 := -i

private def chartInverse (q : ℕ) (x : FourFiber q) : FourFiber q :=
  (-((chi q x.2)⁻¹) * x.1, inverseLayer x.2)

private def chartRelativeDerivative (q : ℕ)
    (σ : Equiv.Perm (FourFiber q)) (g x : FourFiber q) : FourFiber q :=
  σ.symm
    (generalizedQuaternionChartMul q
      (σ (generalizedQuaternionChartMul q x g))
      (chartInverse q (σ g)))

private def projectedDerivativeInversionStep (q : ℕ)
    (σ : Equiv.Perm (FourFiber q)) (x y : FourFiber q) : Prop :=
  (∃ g : FourFiber q, y = chartRelativeDerivative q σ g x) ∨
    y = σ.symm (chartInverse q (σ x))

private def projectedDerivativeInversionAtom (q : ℕ)
    (σ : Equiv.Perm (FourFiber q)) (x : FourFiber q) : Set (FourFiber q) :=
  {y | Relation.ReflTransGen (projectedDerivativeInversionStep q σ) x y}

private def chartAutomorphism (q : ℕ)
    (β : Equiv.Perm (FourFiber q)) : Prop :=
  ∀ x y : FourFiber q,
    β (generalizedQuaternionChartMul q x y) =
      generalizedQuaternionChartMul q (β x) (β y)

/-- Claim 32948: every normalized affine map of the marked Q₄q base has an
ordinary automorphism shadow, with the exact transported derivative/inversion
atom action and pointwise agreement on the characteristic C_q layer. -/
def claim32948 : Prop :=
  ∀ (q : ℕ), (hq : Nat.Prime q) → 2 < q →
    letI : Fact q.Prime := ⟨hq⟩
    ∀ σ : Equiv.Perm (FourFiber q),
      normalizedFiberwiseAffinePresentation q σ →
        ∃ β : Equiv.Perm (FourFiber q),
          chartAutomorphism q β ∧
            (∀ x : FourFiber q,
              Set.image β (projectedDerivativeInversionAtom q σ x) =
                Set.image σ (projectedDerivativeInversionAtom q σ x)) ∧
            (∀ x : ZMod q,
              β (x, (0 : Fin 4)) = σ (x, (0 : Fin 4)))

end

end MathlibPlus.Open.Research.R1060MarkedShadow32948
