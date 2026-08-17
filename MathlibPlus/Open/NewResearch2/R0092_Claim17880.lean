import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0092

noncomputable section

open Module

private def orientedWedgeValue {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ) (x y : V) : ℝ :=
  ω ![x, y]

private def endpointDeterminant {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (a c : ℝ) : ℝ :=
  orientedWedgeValue ω (v a) (v c)

private def endpointDerivativeA {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (a c : ℝ) : ℝ :=
  deriv (fun x => endpointDeterminant ω v x c) a

private def endpointDerivativeC {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (a c : ℝ) : ℝ :=
  deriv (fun y => endpointDeterminant ω v a y) c

private def endpointMixedDerivative {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (a c : ℝ) : ℝ :=
  deriv (fun x => deriv (fun y => endpointDeterminant ω v x y) c) a

private def curveWronskian {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (x : ℝ) : ℝ :=
  orientedWedgeValue ω (v x) (deriv v x)

/-- Claim 17880: for every C² curve in one oriented two-dimensional real
vector space, the endpoint derivatives of the same fixed oriented wedge
satisfy the confluent Plücker identity. -/
def claim17880 : Prop :=
  ∀ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fact (finrank ℝ V = 2)]
    (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ),
    ω ≠ 0 →
    ∀ (v : ℝ → V) (a c : ℝ),
    ContDiff ℝ 2 v →
      endpointDeterminant ω v a c * endpointMixedDerivative ω v a c -
          endpointDerivativeA ω v a c * endpointDerivativeC ω v a c =
        curveWronskian ω v a * curveWronskian ω v c

end
end MathlibPlus.Open.NewResearch2.R0092
