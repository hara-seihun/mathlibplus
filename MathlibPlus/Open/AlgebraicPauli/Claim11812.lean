import MathlibPlus.Open.AlgebraicPauli.Orientation

namespace MathlibPlus.Open.AlgebraicPauli

noncomputable section

/-- The Cartan weight of the `r`th vector in the supplied weight basis. -/
def cartanWeightExponent (n : ℕ) (r : Fin (n + 1)) : ℤ :=
  (n : ℤ) - 2 * (r.1 : ℤ)

/-- The diagonal Cartan operator on one symmetric-power summand. -/
def cartanWeightOperator (n : ℕ) (b : WeightBasis n) :
    SymPower n →ₗ[ℂ] SymPower n :=
  b.constr ℂ (fun r =>
    (cartanWeightExponent n r : ℂ) • b r)

/-- The one-factor zero-weight subspace, expressed in the actual weight basis. -/
def zeroWeightLine (n : ℕ) (b : WeightBasis n) :
    Submodule ℂ (SymPower n) :=
  Submodule.span ℂ
    {v | ∃ r : Fin (n + 1), cartanWeightExponent n r = 0 ∧ v = b r}

/-- The projector onto the zero-weight basis vectors of an even summand. -/
def zeroWeightProjector (n : ℕ) (b : WeightBasis n) :
    SymPower n →ₗ[ℂ] SymPower n :=
  b.constr ℂ (fun r =>
    if cartanWeightExponent n r = 0 then b r else 0)

/-- The diagonal Cartan operator on the two-copy mixed carrier. -/
def mixedCartanOperator (k : ℕ) (b : WeightBasis k) :
    MixedSpace k →ₗ[ℂ] MixedSpace k :=
  (MixedBasis k b).constr ℂ (fun ij =>
    ((cartanWeightExponent k ij.1 + cartanWeightExponent k ij.2 : ℤ) : ℂ) •
      MixedBasis k b ij)

/-- The direct-sum carrier in the Clebsch--Gordan decomposition. -/
abbrev clebschGordanTarget (k : ℕ) :=
  DirectSum (Fin (k + 1)) (fun j => SymPower (2 * j.1))

/-- The direct sum of the zero-weight projectors on the Clebsch--Gordan
summands. -/
def clebschGordanZeroWeightProjector
    (k : ℕ)
    (b : ∀ j : Fin (k + 1), WeightBasis (2 * j.1)) :
    clebschGordanTarget k →ₗ[ℂ] clebschGordanTarget k :=
  DirectSum.lmap (fun j => zeroWeightProjector (2 * j.1) (b j))

/-- The divisor-counting function used by the notation `d(n)`. -/
def divisorCount (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/-- Claim 11812: the actual mixed symmetric-power carrier admits the stated
Clebsch--Gordan direct sum; each even summand has one zero-weight line, the
mixed diagonal-Cartan kernel has the stated dimension, and the opposite
alignment projector becomes the direct sum of those zero-weight projectors. -/
def claim11812 : Prop :=
  ∀ (k p : ℕ), Nat.Prime p →
    ∀ b : WeightBasis k,
      ∃ (e : MixedSpace k ≃ₗ[ℂ] clebschGordanTarget k)
        (summandBasis : ∀ j : Fin (k + 1), WeightBasis (2 * j.1)),
        (∀ j : Fin (k + 1),
          LinearMap.ker (cartanWeightOperator (2 * j.1) (summandBasis j)) =
              zeroWeightLine (2 * j.1) (summandBasis j) ∧
            Module.finrank ℂ
                (LinearMap.ker
                  (cartanWeightOperator (2 * j.1) (summandBasis j))) =
              1) ∧
          Module.finrank ℂ (LinearMap.ker (mixedCartanOperator k b)) =
            k + 1 ∧
          Module.finrank ℂ (LinearMap.ker (mixedCartanOperator k b)) =
            divisorCount (p ^ k) ∧
          e.toLinearMap.comp (oppositeAlignmentProjector k b) =
            (clebschGordanZeroWeightProjector k summandBasis).comp
              e.toLinearMap

end

end MathlibPlus.Open.AlgebraicPauli
