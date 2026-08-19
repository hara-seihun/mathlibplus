import MathlibPlus.Open.NewResearch2.R0092_Claim17880

namespace MathlibPlus.Open.NewResearch2.R0092

noncomputable section

open Module

/-- The fixed oriented wedge evaluated on two vectors. -/
def orientedWedgeValue {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fact (finrank ℝ V = 2)]
    (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ) (x y : V) : ℝ :=
  ω ![x, y]

/-- The endpoint determinant `Δ(a,c)=v(a)∧v(c)` for the fixed orientation. -/
def endpointDeterminant {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fact (finrank ℝ V = 2)]
    (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (a c : ℝ) : ℝ :=
  orientedWedgeValue ω (v a) (v c)

/-- The endpoint derivative `Δ_a`. -/
def endpointDerivativeA {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fact (finrank ℝ V = 2)]
    (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (a c : ℝ) : ℝ :=
  deriv (fun x => endpointDeterminant ω v x c) a

/-- The endpoint derivative `Δ_c`. -/
def endpointDerivativeC {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fact (finrank ℝ V = 2)]
    (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (a c : ℝ) : ℝ :=
  deriv (fun y => endpointDeterminant ω v a y) c

/-- The mixed endpoint derivative `Δ_ac`. -/
def endpointMixedDerivative {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fact (finrank ℝ V = 2)]
    (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (a c : ℝ) : ℝ :=
  deriv (fun x => deriv (fun y => endpointDeterminant ω v x y) c) a

/-- The oriented curve Wronskian `W(x)=v(x)∧v′(x)`. -/
def curveWronskian {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fact (finrank ℝ V = 2)]
    (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (v : ℝ → V) (x : ℝ) : ℝ :=
  orientedWedgeValue ω (v x) (deriv v x)

end
end MathlibPlus.Open.NewResearch2.R0092
