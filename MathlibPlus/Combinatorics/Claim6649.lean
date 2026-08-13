import Mathlib

namespace MathlibPlus.Combinatorics.Claim6649

universe u

/-- The leaf-corona operation: retain the old graph on the left copy and attach
one new pendant leaf on the right copy to each old vertex. -/
def leafCorona {V : Type u} (G : SimpleGraph V) : SimpleGraph (V ⊕ V) where
  Adj := fun x y =>
    match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inl u, Sum.inr v => u = v
    | Sum.inr u, Sum.inl v => u = v
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro x y hxy
    cases x <;> cases y
    · exact G.symm.symm _ _ hxy
    · simpa [eq_comm] using hxy
    · simpa [eq_comm] using hxy
    · exact hxy.elim⟩
  loopless := ⟨by
    intro x
    cases x
    · exact G.loopless.irrefl _
    · simp⟩

/-- The nested vertex type after `k` leaf-corona iterations. -/
def leafCoronaVertex (V : Type u) : ℕ → Type u
  | 0 => V
  | k + 1 => leafCoronaVertex V k ⊕ leafCoronaVertex V k

/-- The graph obtained after iterating the leaf-corona construction `k` times. -/
def leafCoronaIterate {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → SimpleGraph (leafCoronaVertex V k)
  | 0 => G
  | k + 1 => leafCorona (leafCoronaIterate G k)

end MathlibPlus.Combinatorics.Claim6649
