import MathlibPlus.NumberTheory.HardyZ

/-!
# Real-valuedness of Hardy's Z function

Open-registry component of admitted claim 265. The defining normalization lives in
`MathlibPlus.NumberTheory.HardyZ`; this node records the claim that its values on the
real axis are real.
-/

namespace MathlibPlus.Open.NumberTheory

/-- Hardy's normalized Z function has zero imaginary part at every real argument. -/
def hardyZNormalizationRealValued : Prop :=
  ∀ t : ℝ, (MathlibPlus.NumberTheory.hardyZ t).im = 0

end MathlibPlus.Open.NumberTheory
