import MathlibPlus.Open.ResearchFormalization.O0091Claim13477

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.O0091Klein

noncomputable section

open MathlibPlus.Open.ResearchFormalization.O0091Claim13477

/-- The phase gauge from `theta=t log 2`. -/
def phaseP (theta : ℝ) : LocalMatrix := !![
  Complex.exp (Complex.I * (theta : ℂ) / 2), 0;
  0, Complex.exp (-Complex.I * (theta : ℂ) / 2)]

def phaseC (theta : ℝ) : LocalMatrix :=
  phaseP theta * pauliX * Matrix.conjTranspose (phaseP theta)

def phaseY (theta : ℝ) : LocalMatrix :=
  Complex.I • (phaseC theta * pauliZ)

def phaseSegreVector (theta U Phi : ℝ) : QIndex → ℂ := fun p =>
  let u : Fin 2 → ℂ := ![
    Complex.exp ((U : ℂ) / 2),
    Complex.exp (-((U : ℂ) / 2))]
  let v : Fin 2 → ℂ := ![
    Complex.exp (Complex.I * (Phi : ℂ) / 2),
    Complex.exp (-Complex.I * (Phi : ℂ) / 2)]
  (phaseP theta).mulVec u p.1 * v p.2

def phaseSegreExpectation (A : QMatrix) (z : QIndex → ℂ) : ℂ :=
  ∑ p, star (z p) * (A.mulVec z) p

def identity4 : QMatrix := tensor pauliI pauliI

def rh (theta : ℝ) : QMatrix := tensor (phaseC theta) pauliI
def rc : QMatrix := tensor pauliI pauliX
def kleinD (theta : ℝ) : QMatrix := rh theta * rc
def kleinJ : QMatrix := tensor pauliZ pauliY
def kleinN (theta : ℝ) : QMatrix := kleinD theta * kleinJ

def kleinSpanIndependent (theta : ℝ) : Prop :=
  ∀ a b c d : ℂ,
    a • identity4 + b • kleinD theta + c • kleinJ + d • kleinN theta = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0

def phaseKleinAlgebra (theta : ℝ) : Prop :=
  kleinD theta * kleinD theta = identity4 ∧
    kleinJ * kleinJ = identity4 ∧
    kleinN theta * kleinN theta = identity4 ∧
    kleinD theta * kleinJ = kleinJ * kleinD theta ∧
    kleinD theta * kleinN theta = kleinN theta * kleinD theta ∧
    kleinJ * kleinN theta = kleinN theta * kleinJ ∧
    kleinN theta = kleinD theta * kleinJ ∧
    kleinN theta = tensor (phaseY theta) pauliZ ∧
    kleinSpanIndependent theta

def phaseQ (theta x g t : ℝ) : QMatrix :=
  (((2 + x) / 4 : ℝ) : ℂ) • identity4
    - ((1 / 2 : ℝ) : ℂ) • kleinD theta
    - ((g / 4 : ℝ) : ℂ) • kleinJ
    + (t : ℂ) • kleinN theta

/-- Claim 13506: the parameter `t` simultaneously fixes the phase
`theta=t log 2` and is the coefficient of `N`; no independent replacement
coefficient is introduced. -/
def claim13506_commutingKleinAndSegreExpectations : Prop :=
  ∀ (t theta : ℝ), theta = t * Real.log 2 →
    phaseKleinAlgebra theta ∧
      (∀ U Phi : ℝ,
        phaseSegreExpectation identity4 (phaseSegreVector theta U Phi) =
            ((4 * Real.cosh U : ℝ) : ℂ) ∧
          phaseSegreExpectation (kleinD theta)
              (phaseSegreVector theta U Phi) =
            ((4 * Real.cos Phi : ℝ) : ℂ) ∧
          phaseSegreExpectation kleinJ
              (phaseSegreVector theta U Phi) =
            ((-4 * Real.sinh U * Real.sin Phi : ℝ) : ℂ) ∧
          phaseSegreExpectation (kleinN theta)
              (phaseSegreVector theta U Phi) = 0) ∧
      (∀ x g U Phi : ℝ,
        phaseSegreExpectation
            (phaseQ theta x g t) (phaseSegreVector theta U Phi) =
          ((2 + x : ℝ) * Real.cosh U - 2 * Real.cos Phi +
            g * Real.sinh U * Real.sin Phi : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.O0091Klein
