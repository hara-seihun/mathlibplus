import MathlibPlus.Open.Research.FormalizationBatch_01a004d6

namespace MathlibPlus.Open.ResearchFormalization.R2100UnateEquality36916

open MathlibPlus.Open.Research.FormalizationBatch
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

/-- The indicator of the lower vertices of the transitive tournament order. -/
def allEarlierOnes {n : ℕ} (order : Fin n → Fin n)
    (b : Fin n) (x : Cube n) : Bool :=
  if ∀ a : Fin n, a.val < b.val → x (order a) = true then
    true
  else false

/-- A common cube reflection followed by the ordered lexicographic spanning
forest in which vertex `v_b` has outgoing edges to all earlier `v_a`. -/
def lexicographicEqualityShape {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  ∃ σ : Cube n, ∃ order : Fin n → Fin n,
    Function.Bijective order ∧
      ∀ b : Fin n, ∀ x : Cube n,
        directionValue f (order b) (cubeAdd x σ) =
          allEarlierOnes order b x

/-- Claim 36916: under the required C4-free hypothesis, equality in the
sharp globally-unate edge bound is exactly a common reflection of an ordered
lexicographic cube spanning tree. -/
def claim36916 : Prop :=
  ∀ (n : ℕ)
    (f : (i : Fin n) → DirectionDomain n i → Bool),
    globallyUnate f →
      isC4Free (cubeAdjacency f) →
        (selectedEdgeCount f = 2 ^ n - 1 ↔
          lexicographicEqualityShape f)

end

end MathlibPlus.Open.ResearchFormalization.R2100UnateEquality36916
