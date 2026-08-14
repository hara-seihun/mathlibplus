import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

open scoped BigOperators

/-- Positive indices name the variables `x₁, x₂, …` in `ℤ[x₁, x₂, …]`. -/
abbrev Positive := {n : ℕ // 0 < n}

private def oneIndex : Positive := ⟨1, by decide⟩

private def doubledIndex (s : Positive) : Positive :=
  ⟨2 * s.1, by omega⟩

private noncomputable def thetaImage (s : Positive) : MvPolynomial Positive ℤ :=
  ∑ j ∈ Finset.range (s.1 + 1),
    MvPolynomial.C (s.1.choose j : ℤ) *
      MvPolynomial.X ⟨s.1 + j, by omega⟩ *
      (MvPolynomial.X oneIndex) ^ (s.1 - j)

/-- The leaf-corona endomorphism on `ℤ[x₁, x₂, …]`. -/
noncomputable def leafCoronaTheta : MvPolynomial Positive ℤ →+* MvPolynomial Positive ℤ :=
  (MvPolynomial.aeval thetaImage).toRingHom

/-- Claim 6650: the generator formula for the leaf-corona endomorphism. -/
def leafCoronaEndomorphism : Prop :=
  ∀ s : Positive,
    leafCoronaTheta (MvPolynomial.X s) = thetaImage s

private noncomputable def partitionExponent (parts : Multiset Positive) : Positive →₀ ℕ :=
  Finsupp.onFinset parts.toFinset (fun a => parts.count a) (by
    intro a h
    exact (Multiset.mem_toFinset).2 ((Multiset.count_ne_zero).1 h))

private def doubledPartition (parts : Multiset Positive) : Multiset Positive :=
  parts.map doubledIndex

private noncomputable def partitionCoefficient (parts : Multiset Positive) (F : MvPolynomial Positive ℤ) : ℤ :=
  MvPolynomial.coeff (partitionExponent parts) F

/-- Claim 6652: doubling every part recovers the coefficient after applying `Θ`. -/
noncomputable def topDoubledCoefficientRecovery : Prop :=
  (∀ parts : Multiset Positive,
    MvPolynomial.coeff (partitionExponent (doubledPartition parts))
      (leafCoronaTheta (MvPolynomial.monomial (partitionExponent parts) (1 : ℤ))) = 1 ∧
    ∀ ν : Positive →₀ ℕ,
      ν oneIndex = 0 →
      MvPolynomial.coeff ν
          (leafCoronaTheta (MvPolynomial.monomial (partitionExponent parts) (1 : ℤ))) ≠ 0 →
      ν = partitionExponent (doubledPartition parts)) ∧
  ∀ (F : MvPolynomial Positive ℤ) (parts : Multiset Positive),
    partitionCoefficient (doubledPartition parts) (leafCoronaTheta F) =
      partitionCoefficient parts F

end MathlibPlus.Open.FormalizationBatch
