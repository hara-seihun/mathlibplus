import Mathlib

/-!
# Finite prime-jump and analytic-tail extremum principle

A reusable formal version of the jump-envelope mechanism in admitted claim 623.
The comparison profile is right-continuous, starts at zero, decreases strictly
between prime jumps, is negative at every later prime through a handoff, and is
strictly negative on the analytic tail.  These data make the left endpoint the
unique maximizer of any normalized profile whose strict comparison with its
endpoint value is detected by the sign of the comparison profile.
-/

namespace MathlibPlus.NumberTheory.PrimeCounting

/-- A finite check at every post-endpoint prime, combined with strict decrease
between prime jumps and a strict tail estimate, makes the left endpoint the
unique global maximizer of the normalized profile on its right half-line.

`hRightContinuous` records the source claim's right-continuous convention at
jumps.  The proof uses only the resulting values at the jumps together with
strict inter-prime decrease; continuity itself is not needed after those facts
have been supplied. -/
theorem finitePrimeJumpTail_uniqueMax
    (comparison normalized : ℝ → ℝ) (a handoff : ℝ)
    (_hEndpointHandoff : a < handoff)
    (_hRightContinuous : ∀ x, a ≤ x →
      ContinuousWithinAt comparison (Set.Ici x) x)
    (hComparisonAtEndpoint : comparison a = 0)
    (hComparisonDetectsNormalized : ∀ x, a ≤ x →
      (comparison x < 0 ↔ normalized x < normalized a))
    (hInterPrimeDecrease : ∀ x y, a ≤ x → x < y → y ≤ handoff →
      (∀ p : ℕ, p.Prime → ¬ (x < (p : ℝ) ∧ (p : ℝ) ≤ y)) →
      comparison y < comparison x)
    (hFinitePrimeCheck : ∀ p : ℕ, p.Prime → a < (p : ℝ) →
      (p : ℝ) ≤ handoff → comparison p < 0)
    (hStrictTail : ∀ x, handoff ≤ x → comparison x < 0) :
    (∀ x, a ≤ x → normalized x ≤ normalized a) ∧
      ∀ x, a ≤ x → (normalized x = normalized a ↔ x = a) := by
  have hStrict : ∀ x, a < x → normalized x < normalized a := by
    intro x hax
    have hComparisonNegative : comparison x < 0 := by
      by_cases hTail : handoff ≤ x
      · exact hStrictTail x hTail
      · have hxHandoff : x < handoff := lt_of_not_ge hTail
        by_cases hHasPrime :
            ∃ p : ℕ, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ x
        · obtain ⟨p, hpPrime, hap, hpx⟩ := hHasPrime
          have hxNonneg : 0 ≤ x :=
            le_trans (Nat.cast_nonneg p) hpx
          let primesThroughX : Finset ℕ :=
            (Finset.range (Nat.floor x + 1)).filter
              (fun q => q.Prime ∧ a < (q : ℝ))
          have hpFloor : p ≤ Nat.floor x := Nat.le_floor hpx
          have hpMem : p ∈ primesThroughX := by
            simp only [primesThroughX, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hpPrime, hap⟩
          have hNonempty : primesThroughX.Nonempty := ⟨p, hpMem⟩
          let q := primesThroughX.max' hNonempty
          have hqMem : q ∈ primesThroughX :=
            Finset.max'_mem primesThroughX hNonempty
          have hqData : q < Nat.floor x + 1 ∧ q.Prime ∧ a < (q : ℝ) := by
            simpa only [q, primesThroughX, Finset.mem_filter,
              Finset.mem_range] using hqMem
          have hqFloor : q ≤ Nat.floor x := by omega
          have hqLeX : (q : ℝ) ≤ x :=
            le_trans (Nat.cast_le.mpr hqFloor) (Nat.floor_le hxNonneg)
          have hqNegative : comparison q < 0 :=
            hFinitePrimeCheck q hqData.2.1 hqData.2.2
              (le_trans hqLeX (le_of_lt hxHandoff))
          rcases hqLeX.eq_or_lt with hqx | hqx
          · simpa [hqx] using hqNegative
          · have hNoPrimeAfterQ : ∀ r : ℕ, r.Prime →
                ¬ ((q : ℝ) < (r : ℝ) ∧ (r : ℝ) ≤ x) := by
              intro r hrPrime hqr
              have hrFloor : r ≤ Nat.floor x := Nat.le_floor hqr.2
              have har : a < (r : ℝ) := lt_trans hqData.2.2 hqr.1
              have hrMem : r ∈ primesThroughX := by
                simp only [primesThroughX, Finset.mem_filter,
                  Finset.mem_range]
                exact ⟨by omega, hrPrime, har⟩
              have hrq : r ≤ q := by
                simpa only [q] using
                  (Finset.le_max' primesThroughX r hrMem)
              exact (not_lt_of_ge (Nat.cast_le.mpr hrq)) hqr.1
            exact lt_trans
              (hInterPrimeDecrease q x (le_of_lt hqData.2.2) hqx
                (le_of_lt hxHandoff) hNoPrimeAfterQ)
              hqNegative
        · have hNoPrime : ∀ p : ℕ, p.Prime →
              ¬ (a < (p : ℝ) ∧ (p : ℝ) ≤ x) := by
            intro p hpPrime hpRange
            exact hHasPrime ⟨p, hpPrime, hpRange.1, hpRange.2⟩
          have hDecrease := hInterPrimeDecrease a x (le_rfl) hax
            (le_of_lt hxHandoff) hNoPrime
          simpa [hComparisonAtEndpoint] using hDecrease
    exact (hComparisonDetectsNormalized x (le_of_lt hax)).mp
      hComparisonNegative
  constructor
  · intro x hax
    rcases hax.eq_or_lt with hxa | hax'
    · simpa [hxa]
    · exact le_of_lt (hStrict x hax')
  · intro x hax
    constructor
    · intro hxValue
      rcases hax.eq_or_lt with hxa | hax'
      · exact hxa.symm
      · exact False.elim ((hStrict x hax').ne hxValue)
    · intro hxa
      simpa [hxa]

end MathlibPlus.NumberTheory.PrimeCounting
