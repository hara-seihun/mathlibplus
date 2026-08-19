import MathlibPlus.Open.Research.QuaternionBatch

namespace MathlibPlus.Open.Research.R1060Claim32929

open MathlibPlus.Open.Research.QuaternionBatch

noncomputable section

private def inverseLayer (i : Fin 4) : Fin 4 := -i

private def chartInverse (p : ℕ) (x : FourFiber p) : FourFiber p :=
  (-((chi p x.2)⁻¹) * x.1, inverseLayer x.2)

private def transportedRelativeDerivative (p : ℕ)
    (f : Equiv.Perm (FourFiber p))
    (g x : FourFiber p) : FourFiber p :=
  f.symm
    (generalizedQuaternionChartMul p
      (f (generalizedQuaternionChartMul p x g))
      (chartInverse p (f g)))

private def identityFree (p : ℕ)
    (S : Set (FourFiber p)) : Prop :=
  (0, 0) ∉ S

private def inverseClosed (p : ℕ)
    (S : Set (FourFiber p)) : Prop :=
  ∀ x : FourFiber p,
    x ∈ S ↔ chartInverse p x ∈ S

private def derivativeInvariant (p : ℕ)
    (f : Equiv.Perm (FourFiber p))
    (S : Set (FourFiber p)) : Prop :=
  ∀ g : FourFiber p,
    Set.image (transportedRelativeDerivative p f g) S = S

private def chartAutomorphism (p : ℕ)
    (α : Equiv.Perm (FourFiber p)) : Prop :=
  ∀ x y : FourFiber p,
    α (generalizedQuaternionChartMul p x y) =
      generalizedQuaternionChartMul p (α x) (α y)

/-- Every normalized prime generalized-quaternion affine fibre map has an
ordinary-CI automorphism shadow on every identity-free inverse-closed
connection set stable under the normalized right-translation derivatives. -/
def claim32929_primeAffineFiberMapOrdinaryCIHarmless : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) → 2 < p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ f : Equiv.Perm (FourFiber p),
      normalizedFiberwiseAffinePresentation p f →
        ∀ S : Set (FourFiber p),
          identityFree p S →
            inverseClosed p S →
              derivativeInvariant p f S →
                ∃ α : Equiv.Perm (FourFiber p),
                  chartAutomorphism p α ∧
                    Set.image f S = Set.image α S

end

end MathlibPlus.Open.Research.R1060Claim32929
