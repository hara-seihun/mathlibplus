import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5682StarObstruction

noncomputable section

open Sym2

/-- Claim 57046: the complete-graph star family is an exact linear-size
sunflower-free family whose coordinate deletion distance to a forest is
quadratic. All mathematical definitions are theorem-local. -/
def completeGraphStarObstruction_claim57046 : Prop :=
  ∀ M : ℕ, 4 ≤ M →
    let V := Fin M
    let E := {e : Sym2 V // ∃ u v : V, u ≠ v ∧ e = s(u, v)}
    let K := SimpleGraph.completeGraph V
    let A : V → Finset E := fun i =>
      Finset.univ.filter (fun e => e.1 ∈ K.incidenceSet i)
    let G : Finset E → SimpleGraph V := fun F =>
      SimpleGraph.fromRel (fun u v =>
        ∃ e : E, e ∈ F ∧ e.1 = s(u, v))
    (∀ i : V, (A i).card = M - 1) ∧
      (∀ i j : V, i ≠ j → A i ≠ A j) ∧
      (∀ i j k : V,
        i ≠ j → i ≠ k → j ≠ k →
          A i ∩ A j ≠ A i ∩ A k ∧
            A i ∩ A j ≠ A j ∩ A k ∧
            A i ∩ A k ≠ A j ∩ A k) ∧
      (∀ r : ℕ, 3 ≤ r →
        ¬ ∃ I : Fin r → V,
          Function.Injective I ∧
            ∃ core : Finset E,
              ∀ u v : Fin r, u ≠ v → A (I u) ∩ A (I v) = core) ∧
      G Finset.univ = K ∧
      (∀ F : Finset E,
        (G F).IsAcyclic →
          (Finset.univ \ F).card ≥ Nat.choose (M - 1) 2) ∧
      (∃ F : Finset E,
        (G F).IsAcyclic ∧
          (Finset.univ \ F).card = Nat.choose (M - 1) 2 ∧
          F.card = M - 1)

end

end MathlibPlus.Open.ResearchFormalization.R5682StarObstruction
