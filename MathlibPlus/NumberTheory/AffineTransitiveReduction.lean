import Mathlib

namespace MathlibPlus.NumberTheory

/-- Formalization of the affine-reduction and square-free conclusion in claim
40943.  Transitivity is written as reachability by nonnegative iterates of the
map, for every ordered pair of points. -/
theorem claim40943_affine_transitive_reduction
    (m : ℕ) (u t : ZMod m)
    (htrans : ∀ x y : ZMod m, ∃ n : ℕ,
      ((fun z : ZMod m => u * z + t)^[n]) x = y) :
    (∀ p : ℕ, ∀ hp : Nat.Prime p, ∀ hpm : p ∣ m,
      let φ : ZMod m →+* ZMod p := ZMod.castHom hpm (ZMod p)
      let g : ZMod p → ZMod p := fun x => φ u * x + φ t
      (∀ x y : ZMod p, ∃ n : ℕ, (g^[n]) x = y) ∧
        (φ u ≠ 1 →
          g (φ t * (1 - φ u)⁻¹) = φ t * (1 - φ u)⁻¹ ∧
            ¬ (∀ x y : ZMod p, ∃ n : ℕ, (g^[n]) x = y)) ∧
        φ u = 1) ∧
      (Squarefree m → u = 1) := by
  have hprime :
      ∀ p : ℕ, ∀ hp : Nat.Prime p, ∀ hpm : p ∣ m,
        let φ : ZMod m →+* ZMod p := ZMod.castHom hpm (ZMod p)
        let g : ZMod p → ZMod p := fun x => φ u * x + φ t
        (∀ x y : ZMod p, ∃ n : ℕ, (g^[n]) x = y) ∧
          (φ u ≠ 1 →
            g (φ t * (1 - φ u)⁻¹) = φ t * (1 - φ u)⁻¹ ∧
              ¬ (∀ x y : ZMod p, ∃ n : ℕ, (g^[n]) x = y)) ∧
          φ u = 1 := by
    intro p hp hpm
    dsimp only
    let φ : ZMod m →+* ZMod p := ZMod.castHom hpm (ZMod p)
    let g : ZMod p → ZMod p := fun x => φ u * x + φ t
    have hsurj : Function.Surjective φ := by
      simpa [φ] using (ZMod.castHom_surjective hpm)
    have hcomm : ∀ z : ZMod m, φ (u * z + t) = g (φ z) := by
      intro z
      simp only [φ, g, map_add, map_mul]
    have hiterate : ∀ n : ℕ, ∀ z : ZMod m,
        φ ((fun w : ZMod m => u * w + t)^[n] z) =
          (g^[n]) (φ z) := by
      intro n
      induction n with
      | zero => intro z; rfl
      | succ n ih =>
          intro z
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
          congr 1
          exact hcomm z
    have hred : ∀ x y : ZMod p, ∃ n : ℕ, (g^[n]) x = y := by
      intro x y
      obtain ⟨x', hx'⟩ := hsurj x
      obtain ⟨y', hy'⟩ := hsurj y
      obtain ⟨n, hn⟩ := htrans x' y'
      refine ⟨n, ?_⟩
      rw [← hy', ← hx', ← hiterate n x', hn]
    have hnot : ∀ (hne : φ u ≠ 1),
        ¬ (∀ x y : ZMod p, ∃ n : ℕ, (g^[n]) x = y) := by
      intro hne hgt
      letI : Fact p.Prime := ⟨hp⟩
      let x₀ : ZMod p := φ t * (1 - φ u)⁻¹
      have hden : 1 - φ u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hfix : g x₀ = x₀ := by
        change φ u * (φ t * (1 - φ u)⁻¹) + φ t =
          φ t * (1 - φ u)⁻¹
        field_simp [hden]
        ring
      obtain ⟨n, hn⟩ := hgt x₀ (x₀ + 1)
      have hiterate_fix : ∀ n : ℕ, (g^[n]) x₀ = x₀ := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
            rw [Function.iterate_succ_apply, hfix, ih]
      rw [hiterate_fix n] at hn
      have h01 : (0 : ZMod p) = 1 := by
        have hsub := congrArg (fun z : ZMod p => z - x₀) hn
        calc
          0 = x₀ - x₀ := by ring
          _ = (x₀ + 1) - x₀ := hsub
          _ = 1 := by ring
      exact zero_ne_one h01
    have hu_one : φ u = 1 := by
      by_contra hne
      exact hnot hne hred
    refine ⟨hred, ?_, hu_one⟩
    intro hne
    exact ⟨by
      letI : Fact p.Prime := ⟨hp⟩
      let x₀ : ZMod p := φ t * (1 - φ u)⁻¹
      have hden : 1 - φ u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      change φ u * (φ t * (1 - φ u)⁻¹) + φ t =
        φ t * (1 - φ u)⁻¹
      field_simp [hden]
      ring, hnot hne⟩
  constructor
  · exact hprime
  · intro hsq
    have hm0 : m ≠ 0 := hsq.ne_zero
    letI : NeZero m := ⟨hm0⟩
    let a : ℕ := u.val
    have hu_val : (a : ZMod m) = u := by
      simpa [a] using (ZMod.natCast_zmod_val u)
    have pairwise_of_prime_nodup : ∀ l : List ℕ,
        (∀ q ∈ l, Nat.Prime q) → l.Nodup → l.Pairwise Nat.Coprime := by
      intro l
      induction l with
      | nil =>
          intro _ _
          exact List.Pairwise.nil
      | cons q l ih =>
          intro hprime hnodup
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih (fun r hr => hprime r (List.mem_cons_of_mem q hr))
            (List.nodup_cons.mp hnodup).2⟩
          intro r hr
          apply (Nat.coprime_primes (hprime q List.mem_cons_self)
            (hprime r (List.mem_cons_of_mem q hr))).mpr
          intro hqr
          subst r
          exact (List.nodup_cons.mp hnodup).1 hr
    have hpair : m.primeFactorsList.Pairwise Nat.Coprime := by
      apply pairwise_of_prime_nodup
      · intro q hq
        exact Nat.prime_of_mem_primeFactorsList hq
      · exact hsq.nodup_primeFactorsList
    have hmod : a ≡ 1 [MOD m] := by
      rw [← Nat.prod_primeFactorsList hm0]
      apply (Nat.modEq_list_prod_iff hpair).2
      intro i
      let q := m.primeFactorsList.get i
      have hqmem : q ∈ m.primeFactorsList := by
        dsimp [q]
        exact List.get_mem _ i
      have hq : Nat.Prime q := Nat.prime_of_mem_primeFactorsList hqmem
      have hqm : q ∣ m := Nat.dvd_of_mem_primeFactorsList hqmem
      have huq := (hprime q hq hqm).2.2
      have hcast : (a : ZMod q) = (1 : ZMod q) := by
        rw [← ZMod.natCast_zmod_val u] at huq
        simpa [a] using huq
      exact (ZMod.natCast_eq_natCast_iff a 1 q).mp (by simpa using hcast)
    have hcastm : (a : ZMod m) = (1 : ZMod m) := by
      simpa using (ZMod.natCast_eq_natCast_iff a 1 m).mpr hmod
    rw [← hu_val]
    exact hcastm

end MathlibPlus.NumberTheory
