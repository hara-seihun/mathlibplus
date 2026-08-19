import Mathlib

namespace MathlibPlus.Combinatorics.OddTriangleSigning

/-- An `𝔽₂`-signed complete graph whose every triangle has sign sum one is
switching-equivalent to the constant-one signing. With base vertex `r`, the
base-edge formula and the explicit normalized switch are retained. -/
theorem switching_normalizes_complete_graph
    {V : Type*} (r : V) (s : V → V → ZMod 2)
    (hsymm : ∀ i j, s i j = s j i)
    (hdiag : ∀ i, s i i = 0)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      s i j + s j k + s k i = 1) :
    (∀ i j, i ≠ r → j ≠ r → i ≠ j →
      s i j = 1 + s r i + s r j) ∧
    (∃ t : V → ZMod 2, t r = 0 ∧
      (∀ i, i ≠ r → t i = s r i + 1) ∧
      (∀ i j, i ≠ j → s i j + t i + t j = 1)) := by
  classical
  have hadd : ∀ u : ZMod 2, u + u = 0 := by
    intro u
    fin_cases u <;> decide
  have hsolve : ∀ u v w : ZMod 2, u + w + v = 1 →
      w = 1 + u + v := by
    intro u v w h
    calc
      w = w + 0 + 0 := by simp
      _ = w + (u + u) + (v + v) := by rw [hadd u, hadd v]
      _ = (u + w + v) + u + v := by abel
      _ = 1 + u + v := by rw [h]
  have hbase : ∀ i j, i ≠ r → j ≠ r → i ≠ j →
      s i j = 1 + s r i + s r j := by
    intro i j hir hjr hij
    have ht := htri r i j (Ne.symm hir) hij (Ne.symm hjr)
    rw [hsymm j r] at ht
    exact hsolve (s r i) (s r j) (s i j) ht
  have hswitch : ∀ u : ZMod 2, u + (1 + u) = 1 := by
    intro u
    have hu := hadd u
    calc
      u + (1 + u) = 1 + (u + u) := by abel
      _ = 1 := by rw [hu, add_zero]
  refine ⟨hbase, ?_⟩
  let t : V → ZMod 2 := fun i => if i = r then 0 else 1 + s r i
  refine ⟨t, ?_, ?_, ?_⟩
  · simp [t]
  · intro i hir
    simp [t, hir, add_comm]
  · intro i j hij
    by_cases hir : i = r
    · subst i
      have hjr : j ≠ r := by
        intro h
        apply hij
        exact h.symm
      simp only [t, if_pos, if_neg hjr, zero_add, add_zero]
      exact hswitch (s r j)
    by_cases hjr : j = r
    · subst j
      have hir' : i ≠ r := hir
      rw [hsymm i r]
      simp only [t, if_neg hir', if_pos]
      simpa only [zero_add, add_zero] using hswitch (s r i)
    have hformula := hbase i j hir hjr hij
    simp only [t, if_neg hir, if_neg hjr]
    rw [hformula]
    have htriple : ∀ u v : ZMod 2,
        (1 + u + v) + (1 + u) + (1 + v) = 1 := by
      intro u v
      have hu := hadd u
      have hv := hadd v
      have hone : (1 : ZMod 2) + 1 = 0 := by decide
      calc
        (1 + u + v) + (1 + u) + (1 + v) =
            (1 + 1 + 1) + (u + u) + (v + v) := by abel
        _ = 1 := by rw [hu, hv, hone]; simp
    exact htriple (s r i) (s r j)

end MathlibPlus.Combinatorics.OddTriangleSigning
