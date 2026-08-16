import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim60267

abbrev Vector (r : ℕ) := Fin r → ZMod 2
abbrev Group (r : ℕ) := Vector r × ZMod 9

def cayleyCI : Prop :=
  ∀ r : ℕ, (r = 4 ∨ r = 5) →
    ∀ A : Set (Vector r),
      LinearIndepOn (ZMod 2) (id : Vector r → Vector r) A →
      4 ≤ A.ncard → A.ncard ≤ r →
      ∀ c : ZMod 9, addOrderOf c = 9 →
        let S : Set (Group r) :=
          (fun a : Vector r => (a, 0)) '' A ∪ {(0, c), (0, -c)}
        (S ⊆ ({(0, 0)} : Set (Group r))ᶜ ∧
          (∀ s ∈ S, -s ∈ S)) ∧
        ∀ T : Set (Group r),
          T ⊆ ({(0, 0)} : Set (Group r))ᶜ →
          (∀ t ∈ T, -t ∈ T) →
          ∀ e : SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T,
            ∃ α : Group r ≃+ Group r, α '' S = T

end MathlibPlus.Open.Combinatorics.Claim60267
