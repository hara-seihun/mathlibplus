import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- On `C₂³ × C₉`, every normalized involution moving at most four points has
one additive automorphism that shadows it simultaneously on every ordinary
inverse-compatible normalized-derivative orbit. -/
def binaryRankThreeCyclicNineSupportFourInvolutionsHaveOrdinaryOrbitShadow : Prop :=
  let G := (Fin 3 → ZMod 2) × ZMod 9
  ∀ q : G ≃ G,
    q 0 = 0 →
    (∀ x, q (q x) = x) →
    Set.ncard {x : G | q x ≠ x} ≤ 4 →
    ∃ α : G ≃+ G,
      ∀ S : Set G,
        0 ∉ S →
        (∀ x, x ∈ S ↔ -x ∈ S) →
        0 ∉ q '' S →
        (∀ x, x ∈ q '' S ↔ -x ∈ q '' S) →
        (∀ x y, y - x ∈ S ↔ q y - q x ∈ q '' S) →
        α '' S = q '' S

end MathlibPlus.Open.GraphTheory
