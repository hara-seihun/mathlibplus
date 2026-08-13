import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace MathlibPlus.GraphTheory

/-- Claim 53606 (R-4880.1): a surjective finite graph map with connected fibres
and an edge lift over every base edge induces a bijection on connected
components.  The edge-map hypothesis permits an upstairs edge to collapse
inside one fibre or to project to a base edge. -/
theorem localLiftFibrationComponents_claim53606
    {Vup V : Type*} [Finite Vup] [Finite V]
    (Gup : SimpleGraph Vup) (G : SimpleGraph V)
    (pi : Vup → V) (hpi : Function.Surjective pi)
    (hmap : ∀ ⦃x y : Vup⦄, Gup.Adj x y →
      pi x = pi y ∨ G.Adj (pi x) (pi y))
    (hfiber : ∀ v : V,
      (Gup.induce (pi ⁻¹' ({v} : Set V))).Connected)
    (hedge : ∀ ⦃u v : V⦄, G.Adj u v →
      ∃ x y : Vup, pi x = u ∧ pi y = v ∧ Gup.Adj x y) :
    Function.Bijective
      (SimpleGraph.ConnectedComponent.lift
        (fun x : Vup => G.connectedComponentMk (pi x))
        (fun x y p hp => by
          have map_reach : G.Reachable (pi x) (pi y) := by
            induction p with
            | nil => exact .rfl
            | cons h q ih =>
                rcases hmap h with hcollapse | hbase
                · exact hcollapse ▸ ih (SimpleGraph.Walk.IsPath.of_cons hp)
                · exact hbase.reachable.trans (ih (SimpleGraph.Walk.IsPath.of_cons hp))
          exact SimpleGraph.ConnectedComponent.eq.mpr map_reach)) := by
  let F : SimpleGraph.ConnectedComponent Gup →
      SimpleGraph.ConnectedComponent G :=
    SimpleGraph.ConnectedComponent.lift
      (fun x : Vup => G.connectedComponentMk (pi x))
      (fun x y p hp => by
        have map_reach : G.Reachable (pi x) (pi y) := by
          induction p with
          | nil => exact .rfl
          | cons h q ih =>
              rcases hmap h with hcollapse | hbase
              · exact hcollapse ▸ ih (SimpleGraph.Walk.IsPath.of_cons hp)
              · exact hbase.reachable.trans (ih (SimpleGraph.Walk.IsPath.of_cons hp))
        exact SimpleGraph.ConnectedComponent.eq.mpr map_reach)
  have fiber_reach : ∀ (v : V) {x y : Vup}, pi x = v → pi y = v → Gup.Reachable x y := by
    intro v x y hx hy
    let S : Set Vup := pi ⁻¹' ({v} : Set V)
    have hxs : x ∈ S := by
      exact (Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hx))
    have hys : y ∈ S := by
      exact (Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hy))
    have h : (Gup.induce S).Reachable ⟨x, hxs⟩ ⟨y, hys⟩ :=
      (hfiber v).preconnected _ _
    exact h.map (SimpleGraph.Embedding.induce S).toHom
  have lift_walk : ∀ {u v : V} (p : G.Walk u v) {x y : Vup},
      pi x = u → pi y = v → Gup.Reachable x y := by
    intro u v p
    induction p with
    | @nil z =>
        intro x y hx hy
        exact fiber_reach z hx hy
    | @cons a b c h q ih =>
        intro x y hx hy
        obtain ⟨aa, bb, haa, hbb, hab⟩ := hedge h
        have hxa : Gup.Reachable x aa := fiber_reach a hx haa
        have hby : Gup.Reachable bb y := ih hbb hy
        exact hxa.trans (hab.reachable.trans hby)
  constructor
  · intro C D hCD
    refine SimpleGraph.ConnectedComponent.ind₂ (G := Gup)
      (fun x y hxy => ?_) C D hCD
    have hbase : G.connectedComponentMk (pi x) = G.connectedComponentMk (pi y) := by
      simpa [F] using hxy
    have hreach : G.Reachable (pi x) (pi y) :=
      SimpleGraph.ConnectedComponent.exact hbase
    exact SimpleGraph.ConnectedComponent.sound
      (hreach.elim (fun p => lift_walk p rfl rfl))
  · intro C
    refine SimpleGraph.ConnectedComponent.ind (G := G) (fun v => ?_) C
    obtain ⟨x, hx⟩ := hpi v
    refine ⟨Gup.connectedComponentMk x, ?_⟩
    change F (Gup.connectedComponentMk x) = G.connectedComponentMk v
    simp [F, hx]

end MathlibPlus.GraphTheory
