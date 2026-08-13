import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley

namespace MathlibPlus.GraphTheory

/-- The displayed `C₇²` connection set has precisely the vertical-line edge
relation: distinct vertices are adjacent exactly when their first coordinates
agree. In particular, every vertical fibre is a clique. -/
theorem verticalLineCayleyModel_claim31772 :
    let A := ZMod 7 × ZMod 7
    let S : Set A := {z | z.1 = 0 ∧ z.2 ≠ 0}
    let G : SimpleGraph A := SimpleGraph.addCayley S
    (∀ u v : A, G.Adj u v ↔ u ≠ v ∧ u.1 = v.1) ∧
    (∀ x : ZMod 7, ∀ u v : {z : ZMod 7 × ZMod 7 // z.1 = x},
      u ≠ v → G.Adj (u : ZMod 7 × ZMod 7) (v : ZMod 7 × ZMod 7)) := by
  dsimp
  constructor
  · intro u v
    rw [SimpleGraph.addCayley_adj]
    constructor
    · rintro ⟨huv, hmem | hmem⟩
      · simp only [Set.mem_setOf_eq] at hmem
        have hfirst : -u.1 + v.1 = 0 := by simpa using hmem.1
        exact ⟨huv, neg_add_eq_zero.mp hfirst⟩
      · simp only [Set.mem_setOf_eq] at hmem
        have hfirst : -v.1 + u.1 = 0 := by simpa using hmem.1
        exact ⟨huv, (neg_add_eq_zero.mp hfirst).symm⟩
    · rintro ⟨huv, hsame⟩
      refine ⟨huv, Or.inl ?_⟩
      have hfirst : (-u + v).1 = 0 := by
        simp only [Prod.fst_add, Prod.fst_neg]
        exact neg_add_eq_zero.mpr hsame
      have hsecond : (-u + v).2 ≠ 0 := by
        intro hz
        apply huv
        exact Prod.ext hsame (neg_add_eq_zero.mp (by simpa using hz))
      exact ⟨hfirst, hsecond⟩
  · intro x u v huv
    rw [SimpleGraph.addCayley_adj]
    refine ⟨?_, Or.inl ?_⟩
    · intro h
      exact huv (Subtype.ext h)
    · have hsame : (u : ZMod 7 × ZMod 7).1 = (v : ZMod 7 × ZMod 7).1 := by
        exact u.property.trans v.property.symm
      have hfirst : (-(u : ZMod 7 × ZMod 7) + (v : ZMod 7 × ZMod 7)).1 = 0 := by
        simp only [Prod.fst_add, Prod.fst_neg]
        exact neg_add_eq_zero.mpr hsame
      have hsecond : (-(u : ZMod 7 × ZMod 7) + (v : ZMod 7 × ZMod 7)).2 ≠ 0 := by
        intro hz
        apply huv
        apply Subtype.ext
        apply Prod.ext hsame
        exact neg_add_eq_zero.mp (by simpa using hz)
      exact ⟨hfirst, hsecond⟩

end MathlibPlus.GraphTheory
