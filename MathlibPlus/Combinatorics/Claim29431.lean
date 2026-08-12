import Mathlib

namespace MathlibPlus.Combinatorics.Claim29431

/--
An `F₂`-signed complete graph whose every triangle has sign sum one is
switching-equivalent to the constant-one signing.  With base vertex `b`, the
base-edge formula is retained for edges not incident to `b`.
-/
theorem oddTriangleSwitching
    {V : Type*} (b : V) (s : V → V → ZMod 2)
    (hsymm : ∀ i j, s i j = s j i)
    (hdiag : ∀ i, s i i = 0)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      s i j + s j k + s k i = 1) :
    (∀ i j, i ≠ b → j ≠ b → i ≠ j →
      s i j = 1 + s b i + s b j) ∧
    (∃ t : V → ZMod 2, ∀ i j, i ≠ j →
      s i j + t i + t j = 1) := by
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
  have hbase : ∀ i j, i ≠ b → j ≠ b → i ≠ j →
      s i j = 1 + s b i + s b j := by
    intro i j hib hjb hij
    have ht := htri b i j (Ne.symm hib) hij (Ne.symm hjb)
    rw [hsymm j b] at ht
    exact hsolve (s b i) (s b j) (s i j) ht
  have hswitch : ∀ u : ZMod 2, u + (1 + u) = 1 := by
    intro u
    have hu := hadd u
    calc
      u + (1 + u) = 1 + (u + u) := by abel
      _ = 1 := by rw [hu, add_zero]
  refine ⟨hbase, ?_⟩
  let t : V → ZMod 2 := fun i => if i = b then 0 else 1 + s b i
  refine ⟨t, ?_⟩
  intro i j hij
  by_cases hib : i = b
  · subst i
    have hjb : j ≠ b := by
      intro h
      apply hij
      exact h.symm
    simp only [t, if_pos, if_neg hjb, zero_add, add_zero]
    exact hswitch (s b j)
  by_cases hjb : j = b
  · subst j
    have hib' : i ≠ b := hib
    rw [hsymm i b]
    simp only [t, if_neg hib', if_pos]
    simpa only [zero_add, add_zero] using hswitch (s b i)
  have hformula := hbase i j hib hjb hij
  simp only [t, if_neg hib, if_neg hjb]
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
  exact htriple (s b i) (s b j)
end MathlibPlus.Combinatorics.Claim29431
