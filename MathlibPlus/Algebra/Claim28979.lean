import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra

/--
Claim 28979: primitive normalization of a finite family of distinct integral
points on a rational affine axis produces integral axis coordinates.  Those
coordinates are exactly the coefficientwise residue coordinates modulo every
q ≥ 2, so one residue fiber contains at least the ceiling of the average
number of occupied points.  The natural-number expression `(k + q - 1) / q`
is the ceiling of `k / q` for q ≥ 2, and `ZMod q` records coefficientwise
congruence.
-/
theorem claim28979_affineAxisModularPigeonhole
    {n k q : ℕ} (hq : 2 ≤ q)
    (Q₀ D : Fin n → ℤ) (Q : Fin k → Fin n → ℤ)
    (r : Fin k → ℚ)
    (hline : ∀ i a, (Q i a : ℚ) = (Q₀ a : ℚ) + r i * (D a : ℚ))
    (hdistinct : Function.Injective Q)
    (hprimitive : ∃ u : Fin n → ℤ, ∑ a, u a * D a = 1) :
    ∃ c : Fin k → ℤ, ∃ z : ZMod q,
      (∀ i a, Q i a = Q₀ a + c i * D a) ∧
        Function.Injective c ∧
        (k + q - 1) / q ≤ (Finset.univ.filter (fun i : Fin k =>
          (c i : ZMod q) = z)).card ∧
        (∀ i j, ((c i : ZMod q) = (c j : ZMod q)) ↔
          ∀ a, (Q i a : ZMod q) = Q j a) := by
  classical
  have hqpos : 0 < q := by omega
  letI : NeZero q := ⟨by omega⟩
  letI := ZMod.fintype q
  obtain ⟨u, hu⟩ := hprimitive
  let c : Fin k → ℤ := fun i => ∑ a, u a * (Q i a - Q₀ a)
  have hcoord : ∀ i, (c i : ℚ) = r i := by
    intro i
    change ((∑ a, u a * (Q i a - Q₀ a) : ℤ) : ℚ) = r i
    push_cast
    change (∑ a, (u a : ℚ) * ((Q i a : ℚ) - (Q₀ a : ℚ))) = r i
    calc
      (∑ a, (u a : ℚ) * ((Q i a : ℚ) - (Q₀ a : ℚ))) =
          ∑ a, (u a : ℚ) * (r i * (D a : ℚ)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hline i a]
            ring
      _ = r i * (∑ a, (u a : ℚ) * (D a : ℚ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ = r i := by
            have huq : ∑ a, (u a : ℚ) * (D a : ℚ) = 1 := by
              exact_mod_cast hu
            rw [huq, mul_one]
  have haxisInt : ∀ i a, Q i a = Q₀ a + c i * D a := by
    intro i a
    have hrat : (Q i a : ℚ) = (Q₀ a : ℚ) + (c i : ℚ) * (D a : ℚ) := by
      rw [hline i a, hcoord i]
    exact_mod_cast hrat
  have hc_inj : Function.Injective c := by
    intro i j hij
    apply hdistinct
    funext a
    rw [haxisInt i a, haxisInt j a, hij]
  have hresidue : ∀ i j, ((c i : ZMod q) = (c j : ZMod q)) ↔
      ∀ a, (Q i a : ZMod q) = Q j a := by
    intro i j
    constructor
    · intro hc a
      rw [haxisInt i a, haxisInt j a]
      push_cast
      rw [hc]
    · intro hQ
      have hdiff : ∀ a, ((c i - c j : ℤ) : ZMod q) * (D a : ZMod q) = 0 := by
        intro a
        have ha := hQ a
        rw [haxisInt i a, haxisInt j a] at ha
        push_cast at ha
        calc
          ((c i - c j : ℤ) : ZMod q) * (D a : ZMod q) =
              (c i : ZMod q) * (D a : ZMod q) -
                (c j : ZMod q) * (D a : ZMod q) := by
                push_cast
                ring
          _ = 0 := by linear_combination ha
      have hsum : ((c i - c j : ℤ) : ZMod q) *
          ((∑ a, u a * D a : ℤ) : ZMod q) = 0 := by
        push_cast
        rw [Finset.mul_sum]
        have hcast : ((c i - c j : ℤ) : ZMod q) =
            (c i : ZMod q) - (c j : ZMod q) := by
          push_cast
          rfl
        rw [← hcast]
        apply Finset.sum_eq_zero
        intro a ha
        calc
          ((c i - c j : ℤ) : ZMod q) * (((u a : ℤ) : ZMod q) *
              (D a : ZMod q)) =
            ((u a : ℤ) : ZMod q) *
              (((c i - c j : ℤ) : ZMod q) * (D a : ZMod q)) := by ring
          _ = 0 := by rw [hdiff a, mul_zero]
      rw [hu] at hsum
      have hzero : ((c i - c j : ℤ) : ZMod q) = 0 := by simpa using hsum
      exact sub_eq_zero.mp (by exact_mod_cast hzero)
  by_cases hk : k = 0
  · subst k
    have hlt : 0 + q - 1 < q := by omega
    have hceil : (0 + q - 1) / q = 0 := by
      exact Nat.div_eq_of_lt hlt
    refine ⟨c, 0, ?_, ?_, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · rw [hceil]
      exact Nat.zero_le _
    · exact fun i => Fin.elim0 i
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let f : Fin k → ZMod q := fun i => (c i : ZMod q)
    have hmul : Fintype.card (ZMod q) * ((k + q - 1) / q - 1) <
        Fintype.card (Fin k) := by
      rw [ZMod.card]
      simp only [Fintype.card_fin]
      have hx : q ≤ k + q - 1 := by omega
      have hb0 : 1 ≤ (k + q - 1) / q := by
        exact (Nat.le_div_iff_mul_le hqpos).2 (by simpa [one_mul] using hx)
      have hdiv := Nat.div_add_mod (k + q - 1) q
      have hmod : (k + q - 1) % q < q := Nat.mod_lt _ hqpos
      have hrew : q * ((k + q - 1) / q - 1) =
          q * ((k + q - 1) / q) - q := by
        rw [Nat.mul_sub_left_distrib, mul_one]
      rw [hrew]
      omega
    obtain ⟨z, hz⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hmul
    refine ⟨c, z, haxisInt, hc_inj, ?_, hresidue⟩
    have hb : 1 ≤ (k + q - 1) / q := by
      have hx : q ≤ k + q - 1 := by omega
      exact (Nat.le_div_iff_mul_le hqpos).2 (by simpa [one_mul] using hx)
    have hsucc : (k + q - 1) / q - 1 + 1 ≤
        (Finset.univ.filter (fun i : Fin k => (c i : ZMod q) = z)).card :=
      Nat.succ_le_of_lt (by simpa [f] using hz)
    simpa [Nat.sub_add_cancel hb] using hsucc

end MathlibPlus.Algebra
