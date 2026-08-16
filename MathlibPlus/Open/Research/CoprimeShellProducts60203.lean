import Mathlib

namespace MathlibPlus.Open.Research

/-- The ordinary undirected right-Cayley graph determined by a connection set. -/
def rightCayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => ∃ s ∈ S, y = x * s)

/-- Identity-free inverse-closedness for a multiplicative connection set. -/
def identityFreeInvClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  1 ∉ S ∧ ∀ x, x ∈ S → x⁻¹ ∈ S

/-- The valency-10 and complementary valency-73 CI assertions for `C₇ × Q₁₂`. -/
def coprimeShellProducts60203 : Prop :=
  let G := Multiplicative (ZMod 7) × QuaternionGroup 3
  ∀ k : ℕ, (k = 10 ∨ k = 83 - 10) →
    ∀ S T : Set G,
      identityFreeInvClosed S →
      identityFreeInvClosed T →
      Set.ncard S = k →
      Set.ncard T = k →
      Nonempty (SimpleGraph.Iso (rightCayleyGraph S) (rightCayleyGraph T)) →
      ∃ α : G ≃* G, Set.image (α : G → G) S = T

end MathlibPlus.Open.Research
