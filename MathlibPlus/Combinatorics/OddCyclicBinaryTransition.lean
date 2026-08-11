import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 27550.  A cyclic binary word is represented by a Boolean-valued
function on `ZMod n`, with addition by one giving the cyclic successor. -/
theorem oddCyclicBinaryTransition
    (n : ℕ) (hodd : Odd n) (w : ZMod n → Bool)
    (hstart0 : w 0 = false) (hstart1 : w 1 = true)
    (hno00 : ∀ i : ZMod n, ¬ (w i = false ∧ w (i + 1) = false)) :
    (∃ i : ZMod n, w i = false ∧ w (i + 1) = true) ∧
      (∃ i : ZMod n, w i = true ∧ w (i + 1) = false) ∧
      ∃ i : ZMod n, w i = true ∧ w (i + 1) = true := by
  have h01 : ∃ i : ZMod n, w i = false ∧ w (i + 1) = true := by
    refine ⟨0, hstart0, ?_⟩
    simpa using hstart1
  have h10 : ∃ i : ZMod n, w i = true ∧ w (i + 1) = false := by
    have hprev : w (-1 : ZMod n) = true := by
      cases h : w (-1 : ZMod n) with
      | false =>
          exfalso
          apply hno00 (-1 : ZMod n)
          exact ⟨h, by simpa using hstart0⟩
      | true => simpa using h.symm
    refine ⟨-1, hprev, ?_⟩
    simpa using hstart0
  have h11 : ∃ i : ZMod n, w i = true ∧ w (i + 1) = true := by
    by_contra h
    have hno11 : ∀ i : ZMod n, ¬ (w i = true ∧ w (i + 1) = true) := by
      intro i hi
      exact h ⟨i, hi⟩
    have hflip : ∀ i : ZMod n, w (i + 1) = !w i := by
      intro i
      cases hi : w i with
      | false =>
          cases hj : w (i + 1) with
          | false =>
              exfalso
              exact hno00 i ⟨hi, hj⟩
          | true => simp [hi, hj]
      | true =>
          cases hj : w (i + 1) with
          | false => simp [hi, hj]
          | true =>
              exfalso
              exact hno11 i ⟨hi, hj⟩
    let a : ℕ → Bool := fun k => w (k : ZMod n)
    have ha : ∀ k : ℕ, a (k + 1) = !a k := by
      intro k
      dsimp [a]
      simpa only [Nat.cast_add, Nat.cast_one] using hflip (k : ZMod n)
    have halt : ∀ k : ℕ, a k = if k % 2 = 0 then false else true := by
      intro k
      induction k with
      | zero => simp [a, hstart0]
      | succ k ih =>
          rw [ha k, ih]
          by_cases hk : k % 2 = 0
          · have hk' : (k + 1) % 2 = 1 := by omega
            simp [hk, hk']
          · have hk1 : k % 2 = 1 := by omega
            have hk' : (k + 1) % 2 = 0 := by omega
            simp [hk, hk1, hk']
    have hnmod : n % 2 = 1 := by
      rcases hodd with ⟨q, hq⟩
      omega
    have han_true : a n = true := by
      rw [halt n]
      simp [hnmod]
    have han_false : a n = false := by
      simp [a, hstart0]
    rw [han_true] at han_false
    contradiction
  exact ⟨h01, h10, h11⟩

end MathlibPlus.Combinatorics
