import MathlibPlus.Open.Algebra.PathSwitchM0

namespace MathlibPlus.Open.ResearchFormalization.R1863

open MathlibPlus.Open.Algebra.PathSwitchM0

noncomputable section

/-- The rooted pendant-path extension operator on the reviewed marker ring. -/
def N (p : PathRing) : PathRing :=
  A p + zVar * p

/-- The scalar extension seed `E_k = N^k(1)`. -/
def E (k : ℕ) : PathRing :=
  N^[k] (1 : PathRing)

/-- Claim 34341: the exact abstract same-host path-switch carrier. -/
structure SameHostPathSwitch where
  P : PathRing
  Q : PathRing
  U_H : PathRing
  boundary_P : A P = U_H
  boundary_Q : A Q = U_H
  attachment_P : ∀ k : ℕ,
    A (N^[k] P) = A (E k * P)
  attachment_Q : ∀ k : ℕ,
    A (N^[k] Q) = A (E k * Q)
  path_reversal : ∀ k : ℕ,
    A (P * N^[k] Q) = A (Q * N^[k] P)

end

end MathlibPlus.Open.ResearchFormalization.R1863
