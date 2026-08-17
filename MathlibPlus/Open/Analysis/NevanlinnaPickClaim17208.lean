import MathlibPlus.NumberTheory.CompletedZetaRadial

open scoped BigOperators Topology

namespace MathlibPlus.Open.Analysis.NevanlinnaPickClaim17208

open MathlibPlus.NumberTheory.CompletedZetaRadial

noncomputable section

private noncomputable def modularXiTransform (w : ℂ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + Complex.sqrt w) / riemannXi (1 / 2 : ℂ)

private noncomputable def modularWeylCandidate (z : ℂ) : ℂ :=
  deriv modularXiTransform (-z) / modularXiTransform (-z)

private def upperHalfPlane : Set ℂ :=
  {z | 0 < z.im}

private def nevanlinnaOnUpperHalfPlane (m : ℂ → ℂ) : Prop :=
  ∃ M : ℂ → ℂ,
    (∀ z : ℂ, 0 < z.im → M z = m z) ∧
      AnalyticOnNhd ℂ M upperHalfPlane ∧
        ∀ z : ℂ, 0 < z.im → 0 ≤ (M z).im

private def complexPositiveSemidefinite {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  Matrix.IsHermitian A ∧
    ∀ v : Fin N → ℂ,
      0 ≤ (∑ i : Fin N, ∑ j : Fin N,
        star (v i) * A i j * v j).re

private def allFinitePickMatricesPositive (m : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, ∀ z : Fin N → ℂ,
    (∀ j : Fin N, 0 < (z j).im) →
      complexPositiveSemidefinite
        (fun j k : Fin N =>
          (m (z j) - star (m (z k))) /
            (z j - star (z k)))

/-- Claim 17208: the canonical modular Weyl candidate is Nevanlinna exactly
when all finite Pick matrices on the upper half-plane are positive
semidefinite. -/
def nevanlinnaPickCriterion_claim17208 : Prop :=
  nevanlinnaOnUpperHalfPlane modularWeylCandidate ↔
    allFinitePickMatricesPositive modularWeylCandidate

end

end MathlibPlus.Open.Analysis.NevanlinnaPickClaim17208
