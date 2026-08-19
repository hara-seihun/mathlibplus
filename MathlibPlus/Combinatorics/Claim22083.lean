import MathlibPlus.Combinatorics.HandshakeLemma
import Mathlib.Algebra.BigOperators.ModEq

namespace MathlibPlus.Combinatorics

/-- Claim 22083: the parity of the pair-degree sum is the number of
mismatched internal/root bits. -/
theorem sumPairDegrees_modTwo_eq_mismatchCount_claim22083
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (a r d : V → ℕ)
    (ha : ∀ i, a i ≤ 1)
    (hr : ∀ i, r i ≤ 1)
    (hdegree : ∀ i, d i ≡ a i + r i + D.degree i [MOD 2]) :
    (∑ i, d i) ≡ ∑ i, if a i = r i then 0 else 1 [MOD 2] := by
  have hbalanced : Even (∑ i, D.degree i) := by
    rw [handshakeDegreeSum D]
    exact ⟨D.edgeFinset.card, by omega⟩
  have hxor : ∀ i, a i + r i ≡ (if a i = r i then 0 else 1) [MOD 2] := by
    intro i
    have hai := ha i
    have hri := hr i
    by_cases h : a i = r i
    · simp [h, Nat.ModEq]
      omega
    · have hcases : (a i = 0 ∧ r i = 1) ∨ (a i = 1 ∧ r i = 0) := by omega
      rcases hcases with hcases | hcases
      · simp [hcases.1, hcases.2, Nat.ModEq]
      · simp [hcases.1, hcases.2, Nat.ModEq]
  have hpoint : ∀ i, a i + r i + D.degree i ≡
      (if a i = r i then 0 else 1) + D.degree i [MOD 2] := by
    intro i
    exact (Nat.ModEq.add (hxor i) (Nat.ModEq.refl _))
  have hsum := Nat.ModEq.sum (s := Finset.univ) (fun i _hi => hdegree i)
  have hsum_point := Nat.ModEq.sum (s := Finset.univ) (fun i _hi => hpoint i)
  have hbalanced_mod : (∑ i, D.degree i) ≡ 0 [MOD 2] := by
    rw [Nat.ModEq]
    simpa [Nat.even_iff.mp hbalanced]
  have hcancel :
      (∑ i, (if a i = r i then 0 else 1)) + ∑ i, D.degree i ≡
        ∑ i, (if a i = r i then 0 else 1) [MOD 2] := by
    simpa [Finset.sum_add_distrib] using
      (Nat.ModEq.add (Nat.ModEq.refl (∑ i, (if a i = r i then 0 else 1)))
        hbalanced_mod)
  exact hsum.trans (hsum_point.trans (by simpa [Finset.sum_add_distrib] using hcancel))

end MathlibPlus.Combinatorics
