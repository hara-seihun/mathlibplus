import Mathlib

open scoped Topology

namespace MathlibPlus.Open.Analysis.O0341Claim15555

noncomputable section

private def unitDisk : Set ℂ :=
  {z : ℂ | ‖z‖ < 1}

private def rightHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.re}

private noncomputable def cayley (z : ℂ) : ℂ :=
  (z - 1) / (z + 1)

private def boundedAnalyticOn (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f U ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ∈ U → ‖f z‖ ≤ C) ∧
    (∃ z : ℂ, z ∈ U ∧ f z ≠ 0)

private def multiplicityEnumeration
    (U : Set ℂ) (f : ℂ → ℂ) {I : Type*} [Countable I]
    (a : I → ℂ) : Prop :=
  (∀ i : I, a i ∈ U ∧ f (a i) = 0) ∧
    (∀ z : ℂ, z ∈ U →
      (f z = 0 ↔ ∃ i : I, a i = z) ∧
      Set.ncard {i : I | a i = z} = analyticOrderNatAt f z)

/-- Claim 15555: a nonzero bounded analytic disk function has a
multiplicity-safe Blaschke sum, together with the equivalent Cayley-defect
form for the right half-plane.  Countable index types include the finite and
empty zero divisors. -/
def claim15555 : Prop :=
  (∀ {I : Type*} [Countable I] (f : ℂ → ℂ) (a : I → ℂ),
    boundedAnalyticOn unitDisk f →
      multiplicityEnumeration unitDisk f a →
        Summable (fun i : I => 1 - ‖a i‖)) ∧
  (∀ {I : Type*} [Countable I] (f : ℂ → ℂ) (w : I → ℂ),
    boundedAnalyticOn rightHalfPlane f →
      multiplicityEnumeration rightHalfPlane f w →
        (∀ i : I, ‖cayley (w i)‖ < 1) ∧
        Summable (fun i : I => 1 - ‖cayley (w i)‖))

end

end MathlibPlus.Open.Analysis.O0341Claim15555
