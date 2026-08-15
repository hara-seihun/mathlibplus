import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators

/--
Unit algebraic adhesion on every cut for a block-minimal coordinate certificate.
The rows are a finite matrix presented by its row vectors, `block` partitions those
rows into the participating blocks, and `u` is the selected certificate.
-/
def unitAlgebraicAdhesionOnEveryCut
    {𝕜 : Type*} [Field 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [Fintype R] [DecidableEq R]
    {J : Type*} [Fintype J] [DecidableEq J]
    (t : ι)
    (rows : R → ι →₀ 𝕜)
    (block : R → J)
    (u : J → ι →₀ 𝕜) : Prop :=
  (∀ b : J,
      u b ∈ Submodule.span 𝕜 (rows '' {r : R | block r = b})) →
    (∃ scalar : 𝕜, scalar ≠ 0 ∧ ∑ b : J, u b = Finsupp.single t scalar) →
    (∀ K : Finset J, K ⊂ Finset.univ →
      ¬ ∃ scalar : 𝕜, scalar ≠ 0 ∧
        Finsupp.single t scalar ∈ Submodule.span 𝕜 (u '' (K : Set J))) →
    let v : J → ι →₀ 𝕜 := fun b => Finsupp.erase t (u b)
    (Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range v)) = Fintype.card J - 1) ∧
      ∀ I : Finset J, I.Nonempty → I ⊂ Finset.univ →
        LinearIndependent 𝕜 (fun b : (I : Set J) => v b) ∧
        LinearIndependent 𝕜
          (fun b : ((Finset.univ \ I : Finset J) : Set J) => v b) ∧
        Module.finrank 𝕜
            ↥(Submodule.span 𝕜 (v '' (I : Set J)) ⊓
              Submodule.span 𝕜
                (v '' ((Finset.univ \ I : Finset J) : Set J))) = 1 ∧
        (∑ b ∈ I, v b) ≠ 0 ∧
        Submodule.span 𝕜 ({∑ b ∈ I, v b} : Set (ι →₀ 𝕜)) =
          Submodule.span 𝕜 (v '' (I : Set J)) ⊓
            Submodule.span 𝕜
              (v '' ((Finset.univ \ I : Finset J) : Set J))

end MathlibPlus.Open
