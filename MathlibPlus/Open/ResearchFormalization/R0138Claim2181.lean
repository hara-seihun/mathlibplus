import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0138Claim2181

noncomputable section

private abbrev ChannelMatrix := Matrix (Fin 2) (Fin 2) ℝ
private abbrev ChannelVector := EuclideanSpace ℝ (Fin 2)

private def reflectionMatrix (ell : ℝ) : ChannelMatrix :=
  !![Real.cosh (ell / 2), Real.sinh (ell / 2);
    -Real.sinh (ell / 2), -Real.cosh (ell / 2)]

private def channelAction (M : ChannelMatrix) :
    ChannelVector →ₗ[ℝ] ChannelVector :=
  Matrix.toEuclideanLin M

private def hasEigenvalue (M : ChannelMatrix) (value : ℝ) : Prop :=
  ∃ vector : ChannelVector,
    vector ≠ 0 ∧ channelAction M vector = value • vector

private def euclideanSingularPair (M : ChannelMatrix)
    (right left : ChannelVector) (scale : ℝ) : Prop :=
  right ≠ 0 ∧
    left ≠ 0 ∧
    ‖right‖ = 1 ∧
    ‖left‖ = 1 ∧
    channelAction M right = scale • left ∧
    ‖channelAction M right‖ = scale

private def vonMangoldtReal (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

private def primePowerIndex (n : ℕ) : Prop :=
  ∃ (p k : ℕ), Nat.Prime p ∧ 1 ≤ k ∧ n = p ^ k

private def scaledReflection (n : ℕ) : ChannelMatrix :=
  (vonMangoldtReal n / Real.sqrt (n : ℝ)) •
    reflectionMatrix (Real.log (n : ℝ))

private def hasNoncontractiveDirection (M : ChannelMatrix) : Prop :=
  ∃ vector : ChannelVector,
    vector ≠ 0 ∧ ‖channelAction M vector‖ ≥ ‖vector‖

private def plusUnit : ChannelVector :=
  (1 / Real.sqrt 2) •
    (EuclideanSpace.single (0 : Fin 2) 1 +
      EuclideanSpace.single (1 : Fin 2) 1)

private def minusUnit : ChannelVector :=
  (1 / Real.sqrt 2) •
    (EuclideanSpace.single (0 : Fin 2) 1 -
      EuclideanSpace.single (1 : Fin 2) 1)

/-- Claim 2181: the displayed real reflection is an involution with exact
spectral values and Euclidean singular scales.  At a prime-power index the
same two explicit Euclidean directions retain the displayed scaled values
`Λ(n)` and `Λ(n)/n`; the prime-power index is the exact `p^k` carrier rather
than an unconstrained channel witness. -/
def primePowerSourceReflection_claim2181 : Prop :=
  (∀ ell : ℝ,
    let M : ChannelMatrix := reflectionMatrix ell
    M * M = 1 ∧
      (∀ value : ℝ,
        hasEigenvalue M value ↔ value = 1 ∨ value = -1) ∧
      euclideanSingularPair M plusUnit minusUnit (Real.exp (ell / 2)) ∧
      euclideanSingularPair M minusUnit plusUnit (Real.exp (-(ell / 2))) ∧
      hasNoncontractiveDirection M) ∧
    (∀ n : ℕ, primePowerIndex n →
      let M : ChannelMatrix := scaledReflection n
      euclideanSingularPair M plusUnit minusUnit (vonMangoldtReal n) ∧
        euclideanSingularPair M minusUnit plusUnit
          (vonMangoldtReal n / (n : ℝ)) ∧
        hasNoncontractiveDirection (reflectionMatrix (Real.log (n : ℝ))))

end

end MathlibPlus.Open.ResearchFormalization.R0138Claim2181
