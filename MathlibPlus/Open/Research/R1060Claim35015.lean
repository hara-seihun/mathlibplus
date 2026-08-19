import MathlibPlus.Open.Research.QuaternionBatch

namespace MathlibPlus.Open.Research.R1060Claim35015

open MathlibPlus.Open.Research.QuaternionBatch

noncomputable section

private def inverseLayer (i : Fin 4) : Fin 4 := -i

private def chartInverse (n : ℕ) (x : FourFiber n) : FourFiber n :=
  (-((chi n x.2)⁻¹) * x.1, inverseLayer x.2)

private def transportedRelativeDerivative (n : ℕ)
    (f : Equiv.Perm (FourFiber n))
    (g x : FourFiber n) : FourFiber n :=
  f.symm
    (generalizedQuaternionChartMul n
      (f (generalizedQuaternionChartMul n x g))
      (chartInverse n (f g)))

private def identityFree (n : ℕ)
    (S : Set (FourFiber n)) : Prop :=
  (0, 0) ∉ S

private def inverseClosed (n : ℕ)
    (S : Set (FourFiber n)) : Prop :=
  ∀ x : FourFiber n,
    x ∈ S ↔ chartInverse n x ∈ S

private def derivativeInvariant (n : ℕ)
    (f : Equiv.Perm (FourFiber n))
    (S : Set (FourFiber n)) : Prop :=
  ∀ g : FourFiber n,
    Set.image (transportedRelativeDerivative n f g) S = S

private def chartAutomorphism (n : ℕ)
    (α : Equiv.Perm (FourFiber n)) : Prop :=
  ∀ x y : FourFiber n,
    α (generalizedQuaternionChartMul n x y) =
      generalizedQuaternionChartMul n (α x) (α y)

/-- Every normalized odd square-free generalized-quaternion blockwise affine
permutation has one ordinary-CI automorphism shadow on each identity-free
inverse-closed derivative-invariant connection set. -/
def claim35015_squareFreeAffineMapsOrdinaryCIHarmless : Prop :=
  ∀ (n : ℕ), Odd n → Squarefree n →
    ∀ f : Equiv.Perm (FourFiber n),
      normalizedFiberwiseAffinePresentation n f →
        ∀ S : Set (FourFiber n),
          identityFree n S →
            inverseClosed n S →
              derivativeInvariant n f S →
                ∃ α : Equiv.Perm (FourFiber n),
                  chartAutomorphism n α ∧
                    Set.image f S = Set.image α S

end

end MathlibPlus.Open.Research.R1060Claim35015
