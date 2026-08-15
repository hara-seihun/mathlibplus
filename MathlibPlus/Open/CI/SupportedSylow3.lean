import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace MathlibPlus.Open.CI

abbrev C4 := ZMod 4
abbrev F3Vec3 := Fin 3 → ZMod 3
abbrev G := C4 × F3Vec3

def supportedSylow3CayleyCI : Prop :=
  ∀ (S : Set G),
    S ⊆ (({0} : Set C4) ×ˢ (Set.univ : Set F3Vec3)) \ ({(0, 0)} : Set G) →
    S = -S →
    ∀ (T : Set G),
      T ⊆ (Set.univ : Set G) \ ({(0, 0)} : Set G) →
      T = -T →
      (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) →
      ∃ α : AddAut G, α '' S = T

end MathlibPlus.Open.CI
