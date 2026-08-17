import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0644Claim23606

noncomputable section
open Classical

private def pathGraph (m : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun u v =>
    u.val + 1 = v.val ∨ v.val + 1 = u.val)

private def pathExtension (m : ℕ) (S : Finset (Fin m)) :
    SimpleGraph (Option (Fin m)) :=
  SimpleGraph.fromRel (fun u v =>
    match u, v with
    | some a, some b => (pathGraph m).Adj a b
    | none, some b => b ∈ S
    | some a, none => a ∈ S
    | none, none => False)

private def endpointMask (m : ℕ) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter
    (fun i => i.val = 0 ∨ i.val + 1 = m)

private noncomputable def minimumCardEdgeShell
    {V : Type*} [Fintype V] (e : ℕ) (G : SimpleGraph V) : Prop :=
  letI : DecidableEq V := Classical.decEq _
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  G.edgeFinset.card - G.maxDegree = e

private def pathShellMask (m : ℕ) (S : Finset (Fin m)) : Prop :=
  minimumCardEdgeShell (m - 1) (pathExtension m S)

/-- Claim 23606: for the exact path `P_m` and apex attachment, the
minimum-card-edge shell consists precisely of masks of size at least three and
the endpoint pair; the complementary low masks are exactly the stated ones. -/
def pathAttachmentShellCriterion_claim23606 : Prop :=
  ∀ (m : ℕ), 3 ≤ m →
    ∀ S : Finset (Fin m),
      (pathShellMask m S ↔
        3 ≤ S.card ∨ S = endpointMask m) ∧
      (¬ pathShellMask m S ↔
        S.card = 0 ∨ S.card = 1 ∨
          (S.card = 2 ∧ S ≠ endpointMask m))

end

end MathlibPlus.Open.ResearchFormalization.R0644Claim23606
