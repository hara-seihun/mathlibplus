import MathlibPlus.GraphTheory.LabelledCopyCount
import Mathlib.Data.Fintype.BigOperators

namespace MathlibPlus.GraphTheory.Claim43989

private noncomputable local instance graphIsoFintype
    {SourceVertex TargetVertex : Type*}
    [Fintype SourceVertex]
    [Fintype TargetVertex]
    {source : SimpleGraph SourceVertex}
    {target : SimpleGraph TargetVertex} :
    Fintype (source ≃g target) := by
  classical
  exact
    Fintype.ofInjective
      (fun isomorphism : source ≃g target =>
        (isomorphism : SourceVertex → TargetVertex))
      (by
      intro first second equal
      apply RelIso.ext
      exact congrFun equal)

private noncomputable def copyIntoSubgraph
    {PatternVertex HostVertex : Type*}
    {pattern : SimpleGraph PatternVertex}
    {host : SimpleGraph HostVertex}
    (image : host.Subgraph)
    (isomorphism : pattern ≃g image.coe) :
    SimpleGraph.Copy pattern host where
  toHom := image.hom.comp isomorphism.toHom
  injective' := by
    intro first second equal
    apply isomorphism.toEquiv.injective
    apply Subtype.ext
    exact equal

private theorem copyIntoSubgraph_toSubgraph
    {PatternVertex HostVertex : Type*}
    {pattern : SimpleGraph PatternVertex}
    {host : SimpleGraph HostVertex}
    (image : host.Subgraph)
    (isomorphism : pattern ≃g image.coe) :
    (copyIntoSubgraph image isomorphism).toSubgraph = image := by
  simp [copyIntoSubgraph, SimpleGraph.Copy.toSubgraph,
    SimpleGraph.Subgraph.map_comp]

@[simp] private theorem copy_isoToSubgraph_apply_val
    {PatternVertex HostVertex : Type*}
    {pattern : SimpleGraph PatternVertex}
    {host : SimpleGraph HostVertex}
    (copy : SimpleGraph.Copy pattern host)
    (vertex : PatternVertex) :
    ((copy.isoToSubgraph vertex : copy.toSubgraph.verts) : HostVertex) =
      copy vertex := rfl

private theorem cast_subgraphIso_apply_val
    {PatternVertex HostVertex : Type*}
    {pattern : SimpleGraph PatternVertex}
    {host : SimpleGraph HostVertex}
    {source target : host.Subgraph}
    (equal : source = target)
    (isomorphism : pattern ≃g source.coe)
    (vertex : PatternVertex) :
    (((equal ▸ isomorphism) vertex : target.verts) : HostVertex) =
      isomorphism vertex := by
  subst target
  rfl

private noncomputable def copyFiberEquivIso
    {PatternVertex HostVertex : Type*}
    {pattern : SimpleGraph PatternVertex}
    {host : SimpleGraph HostVertex}
    (image : host.Subgraph) :
    { copy : SimpleGraph.Copy pattern host //
        copy.toSubgraph = image }
      ≃
    (pattern ≃g image.coe) where
  toFun copy :=
    copy.property ▸ copy.1.isoToSubgraph
  invFun isomorphism :=
    ⟨copyIntoSubgraph image isomorphism,
      copyIntoSubgraph_toSubgraph image isomorphism⟩
  left_inv copy := by
    rcases copy with ⟨copy, imageEquality⟩
    subst image
    apply Subtype.ext
    apply SimpleGraph.Copy.ext
    intro vertex
    rfl
  right_inv isomorphism := by
    dsimp
    apply RelIso.ext
    intro vertex
    apply Subtype.ext
    rw [cast_subgraphIso_apply_val
        (copyIntoSubgraph_toSubgraph image isomorphism),
      copy_isoToSubgraph_apply_val]
    rfl

private noncomputable def graphIsoEquivSourceAutomorphism
    {SourceVertex TargetVertex : Type*}
    {source : SimpleGraph SourceVertex}
    {target : SimpleGraph TargetVertex}
    (base : source ≃g target) :
    (source ≃g target) ≃ (source ≃g source) where
  toFun isomorphism := base.symm.comp isomorphism
  invFun automorphism := base.comp automorphism
  left_inv isomorphism := by
    apply RelIso.ext
    intro vertex
    simp
  right_inv automorphism := by
    apply RelIso.ext
    intro vertex
    simp

private theorem graphIso_fintypeCard
    {SourceVertex TargetVertex : Type*}
    [Fintype SourceVertex]
    [Fintype TargetVertex]
    {source : SimpleGraph SourceVertex}
    {target : SimpleGraph TargetVertex}
    (isomorphic : Nonempty (source ≃g target)) :
    Fintype.card (source ≃g target) =
      Fintype.card (source ≃g source) :=
  Fintype.card_congr
    (graphIsoEquivSourceAutomorphism isomorphic.some)

/-- Claim 43989: finite labelled copies are unlabelled copies weighted by the
pattern graph's automorphism cardinality. -/
theorem labelledCopyCount_eq_copyCount_mul_automorphismCard_claim43989
    {PatternVertex HostVertex : Type*}
    [Fintype PatternVertex]
    [Fintype HostVertex]
    (pattern : SimpleGraph PatternVertex)
    (host : SimpleGraph HostVertex) :
    host.labelledCopyCount pattern =
      host.copyCount pattern * Fintype.card (pattern ≃g pattern) := by
  classical
  rw [SimpleGraph.labelledCopyCount, SimpleGraph.copyCount]
  calc
    Fintype.card (SimpleGraph.Copy pattern host) =
        Fintype.card
          (Σ image : host.Subgraph,
            { copy : SimpleGraph.Copy pattern host //
              copy.toSubgraph = image }) :=
      Fintype.card_congr
        (Equiv.sigmaFiberEquiv
          (SimpleGraph.Copy.toSubgraph :
            SimpleGraph.Copy pattern host → host.Subgraph)).symm
    _ = ∑ image : host.Subgraph,
        Fintype.card
          { copy : SimpleGraph.Copy pattern host //
            copy.toSubgraph = image } :=
      Fintype.card_sigma
    _ = ∑ image : host.Subgraph,
        Fintype.card (pattern ≃g image.coe) := by
      apply Finset.sum_congr rfl
      intro image _
      exact Fintype.card_congr (copyFiberEquivIso image)
    _ = ∑ image : host.Subgraph,
        if Nonempty (pattern ≃g image.coe)
        then Fintype.card (pattern ≃g pattern)
        else 0 := by
      apply Finset.sum_congr rfl
      intro image _
      by_cases isomorphic : Nonempty (pattern ≃g image.coe)
      · simp [isomorphic, graphIso_fintypeCard isomorphic]
      · have emptyIso : IsEmpty (pattern ≃g image.coe) :=
          ⟨fun isomorphism => isomorphic ⟨isomorphism⟩⟩
        simp [isomorphic]
    _ = Fintype.card
          { image : host.Subgraph //
            Nonempty (pattern ≃g image.coe) } *
        Fintype.card (pattern ≃g pattern) := by
      calc
        (∑ image : host.Subgraph,
            if Nonempty (pattern ≃g image.coe)
            then Fintype.card (pattern ≃g pattern)
            else 0) =
          ((Finset.univ.filter fun image : host.Subgraph =>
            Nonempty (pattern ≃g image.coe)).card) *
            Fintype.card (pattern ≃g pattern) := by
              rw [Finset.sum_ite]
              simp [Finset.sum_const_zero, Finset.sum_const]
        _ = Fintype.card
              { image : host.Subgraph //
                Nonempty (pattern ≃g image.coe) } *
            Fintype.card (pattern ≃g pattern) := by
              rw [Fintype.card_subtype]
    _ = ((Finset.univ.filter fun image : host.Subgraph =>
          Nonempty (pattern ≃g image.coe)).card) *
        Fintype.card (pattern ≃g pattern) := by
      rw [Fintype.card_subtype]

end MathlibPlus.GraphTheory.Claim43989
