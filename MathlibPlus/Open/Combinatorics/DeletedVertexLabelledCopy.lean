import Mathlib.Combinatorics.SimpleGraph.Copy

namespace MathlibPlus.Open.Combinatorics

/-- Claim 44005: deleting each host vertex counts each labelled copy once for
all host vertices outside its image. -/
noncomputable def deletedVertexLabelledCopyIdentity : Prop :=
  ∀ (V W : Type*) [Fintype V] [Fintype W]
    (P : SimpleGraph W) (H : SimpleGraph V),
    (∑ v : V,
      letI : Fintype {x : V | x ≠ v} := Fintype.ofFinite _
      (H.induce {x : V | x ≠ v}).labelledCopyCount P) =
      (Fintype.card V - Fintype.card W) * H.labelledCopyCount P

end MathlibPlus.Open.Combinatorics
