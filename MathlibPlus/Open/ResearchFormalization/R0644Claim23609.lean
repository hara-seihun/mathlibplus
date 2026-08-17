import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0644Claim23609

open scoped BigOperators

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

/-- The minimum-card-edge shell statistic used by the attachment-shell
filtration: edge count minus maximum degree. -/
private noncomputable def minimumCardEdgeShell
    {V : Type*} [Fintype V] (e : ℕ) (G : SimpleGraph V) : Prop :=
  letI : DecidableEq V := Classical.decEq _
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  G.edgeFinset.card - G.maxDegree = e

private def pathShellMask (m : ℕ) (S : Finset (Fin m)) : Prop :=
  minimumCardEdgeShell (m - 1) (pathExtension m S)

private def hostIsoRel {m : ℕ}
    (G H : SimpleGraph (Option (Fin m))) : Prop :=
  Nonempty (G ≃g H)

private def hostGraphSetoid (m : ℕ) :
    Setoid (SimpleGraph (Option (Fin m))) where
  r := hostIsoRel
  iseqv :=
    { refl := by
        intro G
        exact ⟨SimpleGraph.Iso.refl⟩
      symm := by
        intro G H h
        rcases h with ⟨f⟩
        exact ⟨f.symm⟩
      trans := by
        intro G H K h₁ h₂
        rcases h₁ with ⟨f⟩
        rcases h₂ with ⟨g⟩
        exact ⟨f.trans g⟩ }

private abbrev HostClass (m : ℕ) :=
  Quotient (hostGraphSetoid m)

private def hostClass {m : ℕ}
    (G : SimpleGraph (Option (Fin m))) : HostClass m :=
  Quotient.mk (hostGraphSetoid m) G

/-- This is a multiset-free finite presentation of the actual unrooted host
quotient: all shell masks are mapped into graph-isomorphism classes, so
reflection-related and any other isomorphic labelled presentations are counted
once. -/
private noncomputable def pathHostTypes (m : ℕ) : Finset (HostClass m) :=
  letI : DecidableEq (Finset (Fin m)) := Classical.decEq _
  letI : DecidablePred (pathShellMask m) := Classical.decPred _
  letI : DecidableEq (HostClass m) := Classical.decEq _
  ((Finset.univ : Finset (Finset (Fin m))).filter (pathShellMask m)).image
    (fun S => hostClass (pathExtension m S))

private noncomputable def pathHostTypeCount (m : ℕ) : ℕ :=
  (pathHostTypes m).card

/-- The exact all-order census of unrooted path-extension host types in the
minimum-card-edge shell `S_(m-1)`. -/
def exactAllOrderPathShellCensus_claim23609 : Prop :=
  ∀ (m : ℕ), 3 ≤ m →
    (pathHostTypeCount m : ℚ) =
      ((2 : ℚ) ^ m + (2 : ℚ) ^ ((m + 1) / 2) -
        (m : ℚ) * (m + 1 : ℚ) / 2 -
        (((m + 1) / 2 : ℕ) : ℚ)) / 2

end

end MathlibPlus.Open.ResearchFormalization.R0644Claim23609
