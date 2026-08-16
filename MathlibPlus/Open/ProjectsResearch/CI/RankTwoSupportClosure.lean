import Mathlib

namespace MathlibPlus.Open.ProjectsResearch.CI

/-- Claim 60270: rank-two support closure in C4 × F3^3. -/
def rankTwoSupportClosure : Prop :=
  let V := Fin 3 → ZMod 3
  let G := ZMod 4 × V
  ∀ (W : Submodule (ZMod 3) V),
    Module.finrank (ZMod 3) W = 2 →
      ∀ (S : Set G),
        S ⊆
            ((Set.univ : Set (ZMod 4)) ×ˢ (W : Set V)) \ ({0} : Set G) →
        (∀ x, x ∈ S → -x ∈ S) →
          ∀ (T : Set G),
            T ⊆ (Set.univ : Set G) \ ({0} : Set G) →
            (∀ x, x ∈ T → -x ∈ T) →
            SimpleGraph.Iso
                (SimpleGraph.fromRel (fun x y : G => -x + y ∈ S))
                (SimpleGraph.fromRel (fun x y : G => -x + y ∈ T)) →
              ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.ProjectsResearch.CI
