import Mathlib

namespace MathlibPlus.Arithmetic.Claim24860

/-- A partition of `k+1` has at most `k+1` parts, so a scale strictly above
`k+1` remains positive after subtracting the partition length. -/
theorem nonzeroRowScale_claim24860
    (c m k : ℕ) (τ : List ℕ)
    (hscale : k + 1 < c + m - k)
    (hparts : ∀ a ∈ τ, 0 < a)
    (hsum : τ.sum = k + 1) :
    0 < c + m - k - τ.length := by
  have length_le_sum_of_pos : ∀ l : List ℕ, (∀ a ∈ l, 0 < a) →
      l.length ≤ l.sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        intro hpos
        have ha : 1 ≤ a := by
          have := hpos a (by simp)
          omega
        have hpos' : ∀ b ∈ l, 0 < b := by
          intro b hb
          exact hpos b (by simp [hb])
        have ih' := ih hpos'
        calc
          (a :: l).length = l.length + 1 := by simp
          _ ≤ l.sum + 1 := Nat.add_le_add_right ih' 1
          _ ≤ l.sum + a := Nat.add_le_add_left ha _
          _ = (a :: l).sum := by simp [Nat.add_comm]
  have hlen : τ.length ≤ τ.sum := length_le_sum_of_pos τ hparts
  have hlen' : τ.length ≤ k + 1 := by simpa [hsum] using hlen
  have hlt : τ.length < c + m - k := lt_of_le_of_lt hlen' hscale
  exact Nat.sub_pos_of_lt hlt

end MathlibPlus.Arithmetic.Claim24860
