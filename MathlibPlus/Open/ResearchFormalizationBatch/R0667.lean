import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.R0667

noncomputable section

/-- Claim 29488: adjoin one apex to a finite labeled graph and use the mask
as exactly the set of apex neighbors. -/
def apexMaskExtension {B : Type*} [Fintype B]
    (F : SimpleGraph B) (S : Set B) : SimpleGraph (Option B) where
  Adj x y := match x, y with
    | none, none => False
    | none, some b => b ∈ S
    | some a, none => a ∈ S
    | some a, some b => F.Adj a b
  symm := ⟨by
    intro x y h
    cases x with
    | none =>
        cases y with
        | none => exact h
        | some b => exact h
    | some a =>
        cases y with
        | none => exact h
        | some b => exact F.symm.symm a b h
  ⟩
  loopless := ⟨by
    intro x h
    cases x with
    | none => exact h
    | some b => exact F.loopless.irrefl b h
  ⟩

def deleteGraph {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (D : Finset V) : SimpleGraph {x // x ∉ D} where
  Adj x y := G.Adj x.1 y.1
  symm := ⟨by
    intro x y h
    exact G.symm.symm _ _ h
  ⟩
  loopless := ⟨by
    intro x h
    exact G.loopless.irrefl _ h
  ⟩

def graphIsomorphic {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

/-- Claim 29490: the marked transverse deletion certificate, with all four
vertices (including the apex) pairwise distinct. -/
structure MarkedTransverseCertificate
    {B P K : Type*} [Fintype B] [DecidableEq B]
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B) where
  u : Option B
  v : Option B
  w : Option B
  apex_u : u ≠ none
  apex_v : v ≠ none
  apex_w : w ≠ none
  u_v : u ≠ v
  u_w : u ≠ w
  v_w : v ≠ w
  alpha : graphIsomorphic Pgraph (deleteGraph (apexMaskExtension F S) {u})
  beta : graphIsomorphic Kgraph (deleteGraph (apexMaskExtension F S) {v, w})

end
end MathlibPlus.Open.ResearchFormalizationBatch.R0667
