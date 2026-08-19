import MathlibPlus.Open.ResearchFormalizationBatch01_01a001be

namespace MathlibPlus.Open.ResearchFormalization.Claim7127

open scoped BigOperators

noncomputable section

abbrev PrimeIndex (n : ℕ) :=
  MathlibPlus.Open.ResearchFormalizationBatch.Claim7131.PrimeIndex n

abbrev TensorIndex (n : ℕ) :=
  MathlibPlus.Open.ResearchFormalizationBatch.Claim7131.TensorIndex n

abbrev TensorCarrier (n : ℕ) :=
  MathlibPlus.Open.ResearchFormalizationBatch.Claim7131.StateSpace n

abbrev PacketMatrix (n : ℕ) :=
  Matrix (TensorIndex n) (TensorIndex n) ℂ

/-- The local log-prime Cartan weight in the canonical tensor-coordinate
basis supplied by Claim 7131. -/
def localWeight (n : ℕ) (i : TensorIndex n) (p : PrimeIndex n) : ℂ :=
  (Real.log (p.1 : ℝ) : ℂ) *
    (MathlibPlus.Open.ResearchFormalizationBatch.Claim7131.exponentDifference
      n i p : ℂ)

def globalWeight (n : ℕ) (i : TensorIndex n) : ℂ :=
  ∑ p : PrimeIndex n, localWeight n i p

/-- The independently specified global reversal, Cartan, and skew-current
matrices.  The last is the action of `Y=-JH` before the tensor expansion. -/
def globalReversalMatrix (n : ℕ) : PacketMatrix n :=
  fun i j =>
    if i =
        MathlibPlus.Open.ResearchFormalizationBatch.Claim7131.reverseIndex n j
    then 1
    else 0

def globalCartanMatrix (n : ℕ) : PacketMatrix n :=
  fun i j => if i = j then globalWeight n i else 0

def globalSkewCurrentMatrix (n : ℕ) : PacketMatrix n :=
  -(globalReversalMatrix n * globalCartanMatrix n)

/-- The coordinate matrix of the prime-ordered tensor product of the local
reversals `J_k`. -/
def tensorReversalMatrix (n : ℕ) : PacketMatrix n :=
  fun i j =>
    ∏ p : PrimeIndex n,
      if i p =
          (MathlibPlus.Open.ResearchFormalizationBatch.Claim7131.reverseIndex n j) p
      then 1
      else 0

/-- One prime-local summand of the restricted tensor Cartan operator. -/
def tensorCartanTerm (n : ℕ) (p : PrimeIndex n) : PacketMatrix n :=
  fun i j => if i = j then localWeight n i p else 0

def tensorCartanMatrix (n : ℕ) : PacketMatrix n :=
  ∑ p : PrimeIndex n, tensorCartanTerm n p

/-- One prime-local summand of the restricted tensor `-J_k H_k` operator.
Its matrix entry is the coordinate form of `-J_k H_k` on the local basis. -/
def tensorSkewCurrentTerm (n : ℕ) (p : PrimeIndex n) : PacketMatrix n :=
  fun i j =>
    if i =
        MathlibPlus.Open.ResearchFormalizationBatch.Claim7131.reverseIndex n j
    then -localWeight n j p
    else 0

def tensorSkewCurrentMatrix (n : ℕ) : PacketMatrix n :=
  ∑ p : PrimeIndex n, tensorSkewCurrentTerm n p

/-- Claim 7127: on the canonical prime-factorization tensor-coordinate
carrier, the independently specified global operators are exactly the
prime-ordered tensor reversal, log-prime Cartan sum, and skew-current sum. -/
def claim_7127 : Prop :=
  ∀ n : ℕ, 1 < n →
    globalReversalMatrix n = tensorReversalMatrix n ∧
      globalCartanMatrix n = tensorCartanMatrix n ∧
      globalSkewCurrentMatrix n = tensorSkewCurrentMatrix n

end

end MathlibPlus.Open.ResearchFormalization.Claim7127
