import MathlibPlus.Open.FormalizationBatchK0145

namespace MathlibPlus.Open.FormalizationBatchK0145

/-- The exact number of graph-isomorphism classes of order-24 `R(4,5)` graphs. -/
def claim9141 : Prop :=
  Fintype.card {c : GraphClass24 // ClassHasR45 c} = 352366

end MathlibPlus.Open.FormalizationBatchK0145
