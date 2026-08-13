import Mathlib

namespace MathlibPlus.Combinatorics

/-- The explicit three-coordinate counterexample to the one-fiber product
lower bound.  The displayed integers are represented by their little-endian
supports on `Fin 3`; `⊎` is the pairwise-union product of two families. -/
theorem oneFiberModuleProductLowerBound_counterexample_claim42279 :
    let Ω := Fin 3
    let z : Finset Ω := ∅
    let m1 : Finset Ω := {0}
    let m2 : Finset Ω := {1}
    let m3 : Finset Ω := {0, 1}
    let m5 : Finset Ω := {0, 2}
    let m6 : Finset Ω := {1, 2}
    let m7 : Finset Ω := {0, 1, 2}
    let H₀ : Finset (Finset Ω) := {z, m1, m2, m3, m5, m7}
    let H₁ : Finset (Finset Ω) := {m3, m5, m6, m7}
    let H₂ : Finset (Finset Ω) := H₁
    let product : Finset (Finset Ω) → Finset (Finset Ω) → Finset (Finset Ω) :=
      fun A B => (A.product B).image (fun p => p.1 ∪ p.2)
    (∀ s ∈ H₀, ∀ t ∈ H₀, s ∪ t ∈ H₀) ∧
    (∀ s ∈ H₁, ∀ t ∈ H₁, s ∪ t ∈ H₁) ∧
    (∀ s ∈ H₂, ∀ t ∈ H₂, s ∪ t ∈ H₂) ∧
    z ∈ H₀ ∧
    product H₀ H₁ = H₁ ∧
    product H₀ H₂ = H₂ ∧
    (∀ s ∈ H₁, 2 ≤ s.card) ∧
    (m3 ∩ m5 ∩ m6 = ∅) ∧
    product H₁ H₂ = H₁ ∧
    (product H₁ H₂).card < H₀.card - 1 := by
  dsimp
  repeat' constructor
  all_goals native_decide +revert

end MathlibPlus.Combinatorics
