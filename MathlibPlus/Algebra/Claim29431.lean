import Mathlib.Tactic

namespace MathlibPlus
namespace Algebra

/--
The exact triangle-signing identity from claim 29431.  A base vertex is
represented by the explicit `Fin n` element `⟨0, hn⟩`; the conclusion is only
asserted for distinct vertices away from that base, exactly as required by the
triangle hypotheses.
-/
theorem oddTriangleSwitchingFormula_claim29431
    {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n → ZMod 2)
    (hsym : ∀ a b, s a b = s b a)
    (htri : ∀ ⦃a b c : Fin n⦄, a ≠ b → b ≠ c → a ≠ c →
      s a b + s b c + s c a = 1) {i j : Fin n}
    (hi : i ≠ ⟨0, hn⟩) (hj : j ≠ ⟨0, hn⟩) (hij : i ≠ j) :
    s i j = 1 + s ⟨0, hn⟩ i + s ⟨0, hn⟩ j := by
  have h0i : (⟨0, hn⟩ : Fin n) ≠ i := by exact Ne.symm hi
  have h0j : (⟨0, hn⟩ : Fin n) ≠ j := by exact Ne.symm hj
  have h := htri h0i hij h0j
  rw [hsym j ⟨0, hn⟩] at h
  have add_self (u : ZMod 2) : u + u = 0 := by
    calc
      u + u = (2 : ZMod 2) * u := by ring
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  calc
    s i j = s i j + (s ⟨0, hn⟩ i + s ⟨0, hn⟩ i) +
        (s ⟨0, hn⟩ j + s ⟨0, hn⟩ j) := by
          rw [add_self (s ⟨0, hn⟩ i), add_self (s ⟨0, hn⟩ j)]
          simp
    _ = (s ⟨0, hn⟩ i + s i j + s ⟨0, hn⟩ j) +
        s ⟨0, hn⟩ i + s ⟨0, hn⟩ j := by ring
    _ = 1 + s ⟨0, hn⟩ i + s ⟨0, hn⟩ j := by rw [h]

end Algebra
end MathlibPlus
