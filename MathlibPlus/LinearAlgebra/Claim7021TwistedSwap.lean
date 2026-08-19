import MathlibPlus.Open.Research.FormalizationBatch01a000ea

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra

noncomputable section

abbrev TensorSpace7021 (n : MathlibPlus.Open.Research.PosNat) :=
  (MathlibPlus.Open.Research.divisorIndex n ×
      MathlibPlus.Open.Research.divisorIndex n) → ℂ

/-- The tensor square of the divisor-complement involution from Claim 7020. -/
def tensorDivisorInvolution7021
    (n : MathlibPlus.Open.Research.PosNat) (v : TensorSpace7021 n) : TensorSpace7021 n :=
  fun p =>
    v (MathlibPlus.Open.Research.divisorComplement n p.1,
      MathlibPlus.Open.Research.divisorComplement n p.2)

/-- The operator swapping the two tensor coordinates. -/
def tensorSwap7021
    (n : MathlibPlus.Open.Research.PosNat) (v : TensorSpace7021 n) : TensorSpace7021 n :=
  fun p => v (p.2, p.1)

/-- `(J_n ⊗ J_n) S_n`, with both factors written on the divisor-indexed basis. -/
def twistedSwap7021
    (n : MathlibPlus.Open.Research.PosNat) (v : TensorSpace7021 n) : TensorSpace7021 n :=
  tensorDivisorInvolution7021 n (tensorSwap7021 n v)

/-- The coordinate Hilbert inner product on the finite tensor carrier. -/
def divisorIndexFinset7021
    (n : MathlibPlus.Open.Research.PosNat) :
    Finset (MathlibPlus.Open.Research.divisorIndex n) :=
  (MathlibPlus.Open.Research.positiveDivisors n).attach

/-- The coordinate Hilbert inner product on the finite tensor carrier. -/
def tensorInner7021
    (n : MathlibPlus.Open.Research.PosNat)
    (u v : TensorSpace7021 n) : ℂ :=
  ∑ p ∈ (divisorIndexFinset7021 n).product (divisorIndexFinset7021 n),
    star (u p) * v p

/-- Self-adjointness and involutivity of the explicitly defined twisted swap. -/
def twistedSwap_selfAdjoint_involution_claim7021 : Prop :=
  ∀ n : MathlibPlus.Open.Research.PosNat,
    (∀ u v : TensorSpace7021 n,
      tensorInner7021 n (twistedSwap7021 n u) v =
        tensorInner7021 n u (twistedSwap7021 n v)) ∧
    (∀ u : TensorSpace7021 n,
      twistedSwap7021 n (twistedSwap7021 n u) = u)

end

end MathlibPlus.LinearAlgebra
