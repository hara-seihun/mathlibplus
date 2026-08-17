import MathlibPlus.NumberTheory.CompletedZetaRadial

open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.R0015NevanlinnaExtension

noncomputable section

open MathlibPlus.NumberTheory.CompletedZetaRadial

/-- The modular xi transform used by the admitted Weyl candidate. -/
def modularXiTransform (w : ℂ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + Complex.sqrt w) / riemannXi (1 / 2 : ℂ)

/-- The shifted logarithmic derivative `m(z)=H'(-z)/H(-z)`. -/
def modularWeylCandidate (z : ℂ) : ℂ :=
  deriv modularXiTransform (-z) / modularXiTransform (-z)

/-- The upper half-plane. -/
def upperHalfPlane : Set ℂ :=
  {z | 0 < z.im}

/-- Meromorphic/holomorphic Nevanlinna extension in the packet's sign
convention. -/
def nevanlinnaExtension (m : ℂ → ℂ) : Prop :=
  ∃ M : ℂ → ℂ,
    (∀ z : ℂ, 0 < z.im → M z = m z) ∧
      AnalyticOnNhd ℂ M upperHalfPlane ∧
        ∀ z : ℂ, 0 < z.im → 0 ≤ (M z).im

/-- Claim 17207: RH is equivalent to the Nevanlinna extension of the
specific modular logarithmic-derivative candidate. -/
def claim17207_rh_nevanlinna_extension : Prop :=
  RiemannHypothesis ↔ nevanlinnaExtension modularWeylCandidate

end

end MathlibPlus.Open.ResearchFormalization.R0015NevanlinnaExtension
