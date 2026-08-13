import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every ordinary undirected Cayley graph on `C₂³ × C₉` of valency at most 14
is CI. -/
def binaryRankThreeCyclicNineValencyAtMostFourteenCI : Prop :=
  let V := (Fin 3 → ZMod 2) × ZMod 9
  ∀ (S T : Set V),
    S = -S →
    T = -T →
    0 ∉ S →
    0 ∉ T →
    Set.ncard S ≤ 14 →
    Set.ncard T ≤ 14 →
    Nonempty (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) →
    ∃ α : V ≃+ V, α '' S = T

end MathlibPlus.Open.GraphTheory
