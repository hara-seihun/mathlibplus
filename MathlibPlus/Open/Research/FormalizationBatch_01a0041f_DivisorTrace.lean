import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

abbrev DivisorIndex (n : ℕ) := {d // d ∈ n.divisors}

/-- The positive diagonal weight appearing in the divisor tensor. -/
def divisorWeight (n : ℕ) (d : DivisorIndex n) : ℝ :=
  Real.rpow (((d.1 : ℝ) ^ 2) / (n : ℝ)) ((11 : ℝ) / 2)

/-- Matrix of the diagonal operator `T_n` in the divisor basis. -/
def divisorT (n : ℕ) : Matrix (DivisorIndex n) (DivisorIndex n) ℝ :=
  fun d e => if d = e then divisorWeight n d else 0

/-- Matrix of the divisor-complement involution in that basis. -/
def divisorJ (n : ℕ) : Matrix (DivisorIndex n) (DivisorIndex n) ℝ :=
  fun d e => if d.1 * e.1 = n then 1 else 0

/-- Kronecker product of two square matrices. -/
def tensorMatrix {ι κ R : Type*} [Fintype ι] [Fintype κ] [Semiring R]
    (M : Matrix ι ι R) (N : Matrix κ κ R) : Matrix (ι × κ) (ι × κ) R :=
  fun a b => M a.1 b.1 * N a.2 b.2

/-- The factor swap on the tensor basis. -/
def divisorSwap (n : ℕ) : Matrix (DivisorIndex n × DivisorIndex n)
    (DivisorIndex n × DivisorIndex n) ℝ :=
  fun a b => if a.1 = b.2 ∧ a.2 = b.1 then 1 else 0

def divisorOmega (n : ℕ) : Matrix (DivisorIndex n × DivisorIndex n)
    (DivisorIndex n × DivisorIndex n) ℝ :=
  tensorMatrix (divisorJ n) (divisorJ n) * divisorSwap n

def divisorTwistedTraceMatrix (n : ℕ) : Matrix (DivisorIndex n × DivisorIndex n)
    (DivisorIndex n × DivisorIndex n) ℝ :=
  tensorMatrix (divisorT n) (divisorT n) * divisorOmega n

def matrixTrace {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (M : Matrix ι ι R) : R := ∑ i, M i i

def matrixBasisFixed {ι : Type*} (M : Matrix ι ι ℝ) (i : ι) : Prop := by
  classical
  exact ∀ j, M j i = if j = i then 1 else 0

/-- Twisted divisor trace equals the divisor-counting function. -/
def claim_7022 : Prop :=
  ∀ n : ℕ, 0 < n →
    (∀ d e : DivisorIndex n,
      (matrixBasisFixed (divisorOmega n) (d, e) ↔ d.1 * e.1 = n) ∧
      (matrixBasisFixed (divisorOmega n) (d, e) →
        divisorWeight n d * divisorWeight n e = 1)) ∧
    matrixTrace (divisorTwistedTraceMatrix n) = (n.divisors.card : ℝ)

end
end MathlibPlus.Open.Research
