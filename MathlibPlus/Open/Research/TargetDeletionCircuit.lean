import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research

/--
Target deletion sends a block-minimal delta certificate to a pointed linear
circuit, with the singleton case separated explicitly.
-/
def targetDeletionProducesLinearCircuit : Prop :=
  ∀ {K : Type*} [Field K]
    {Row Coord Block : Type*}
    [Fintype Row] [Fintype Coord] [Fintype Block]
    [DecidableEq Coord] [DecidableEq Block]
    (A : Matrix Row Coord K) (blockOf : Row → Block)
    (hpartition : Function.Surjective blockOf)
    (S : Finset Coord) (t : Coord) (ht : t ∈ S)
    (J : Finset Block) (u : Block → ({c : Coord // c ∈ S} → K)) (lambda : K),
    lambda ≠ 0 ∧
      (∀ b ∈ J,
        u b ∈ Submodule.span K
          {x : ({c : Coord // c ∈ S} → K) |
            ∃ r : Row, blockOf r = b ∧ x = (fun c => A r c.1)}) ∧
      J.sum u = lambda •
        (fun c : {c : Coord // c ∈ S} => if c.1 = t then (1 : K) else 0) ∧
      (∀ I : Finset Block, I ⊂ J →
        ¬ ∃ w : Block → ({c : Coord // c ∈ S} → K),
          (∀ b ∈ I,
            w b ∈ Submodule.span K
              {x : ({c : Coord // c ∈ S} → K) |
                ∃ r : Row, blockOf r = b ∧ x = (fun c => A r c.1)}) ∧
          ∃ μ : K, μ ≠ 0 ∧
            I.sum w = μ •
              (fun c : {c : Coord // c ∈ S} => if c.1 = t then (1 : K) else 0)) →
      let v : Block → ({c : Coord // c ∈ S.erase t} → K) :=
        fun b c => u b ⟨c.1, (Finset.mem_erase.mp c.2).2⟩
      (J.sum v = 0) ∧
        ((2 ≤ J.card) →
          (∀ I : Finset Block, I ⊂ J →
            LinearIndependent K (fun b : {b : Block // b ∈ I} => v b.1)) ∧
          ¬ LinearIndependent K (fun b : {b : Block // b ∈ J} => v b.1) ∧
          Module.finrank K
              (Submodule.span K
                (Set.range (fun b : {b : Block // b ∈ J} => v b.1))) = J.card - 1) ∧
        ((J.card = 1) → ∀ b ∈ J, v b = 0)

end MathlibPlus.Open.Research
